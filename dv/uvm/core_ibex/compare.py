#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''
A script to compare an ISS and RTL run to make sure nothing has diverged.
'''

import argparse
import os
import re
import sys
from typing import Dict, Optional, TextIO, Tuple

from test_entry import TestEntry, get_test_entry

_CORE_IBEX = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_CORE_IBEX, '../../..'))
_RISCV_DV_ROOT = os.path.join(_IBEX_ROOT, 'vendor/google_riscv-dv')
_OLD_SYS_PATH = sys.path

# Import riscv_trace_csv and lib from _DV_SCRIPTS before putting sys.path back
# as it started.
try:
    sys.path = ([os.path.join(_CORE_IBEX, 'riscv_dv_extension'),
                 os.path.join(_RISCV_DV_ROOT, 'scripts')] +
                sys.path)

    from spike_log_to_trace_csv import process_spike_sim_log  # type: ignore
    from ovpsim_log_to_trace_csv import process_ovpsim_sim_log  # type: ignore
    from instr_trace_compare import compare_trace_csv  # type: ignore

    from ibex_log_to_trace_csv import (process_ibex_sim_log,  # type: ignore
                                       check_ibex_uvm_log)
finally:
    sys.path = _OLD_SYS_PATH


_TestAndSeed = Tuple[str, int]
_CompareResult = Tuple[bool, Optional[str], Dict[str, str]]


def read_test_dot_seed(arg: str) -> _TestAndSeed:
    '''Read a value for --test-dot-seed'''

    match = re.match(r'([^.]+)\.([0-9]+)$', arg)
    if match is None:
        raise argparse.ArgumentTypeError('Bad --test-dot-seed ({}): '
                                         'should be of the form TEST.SEED.'
                                         .format(arg))

    return (match.group(1), int(match.group(2), 10))


def compare_test_run(test: TestEntry,
                     idx: int,
                     seed: int,
                     rtl_log_dir: str,
                     iss: str,
                     iss_log_dir: str) -> _CompareResult:
    '''Compare results for a single run of a single test

    Here, test is a dictionary describing the test (read from the testlist YAML
    file). idx is the iteration index and seed is the corresponding seed. iss
    is the chosen instruction set simulator (currently supported: spike and
    ovpsim).

    rtl_log_dir is the directory containing log output from the RTL simulation.
    iss_log_dir is the directory that contains logs for ISS runs.

    Returns a _CompareResult with a pass/fail flag, together with some
    information about the run (to be written to the log file).

    '''
    test_name = test['test']
    assert isinstance(test_name, str)
    uvm_log = os.path.join(rtl_log_dir, 'sim.log')

    kv_data = {
        'test name': test_name,
        'iteration': str(idx),
        'seed': str(seed),
        'UVM log': uvm_log
    }

    # Have a look at the UVM log. Report a failure if an issue is seen in the
    # log.
    uvm_pass, uvm_log_lines = check_ibex_uvm_log(uvm_log)
    if not uvm_pass:
        return (False, 'simulation error', kv_data)

    rtl_log = os.path.join(rtl_log_dir, 'trace_core_00000000.log')
    rtl_csv = os.path.join(rtl_log_dir, 'trace_core_00000000.csv')

    kv_data['rtl log'] = rtl_log
    kv_data['rtl csv'] = rtl_csv
    try:
        # Convert the RTL log file to a trace CSV.
        process_ibex_sim_log(rtl_log, rtl_csv, 1)
    except (OSError, RuntimeError) as e:
        return (False, f'RTL log processing failed ({e})', kv_data)

    no_post_compare = test.get('no_post_compare', False)
    assert isinstance(no_post_compare, bool)

    # no_post_compare skips the final ISS v RTL log check, so if we've reached
    # here we're done when no_post_compare is set.
    if no_post_compare:
        return (True, None, kv_data)

    # There were no UVM errors. Process the log file from the ISS.
    iss_log = os.path.join(iss_log_dir, '{}.{}.log'.format(test_name, idx))
    iss_csv = os.path.join(iss_log_dir, '{}.{}.csv'.format(test_name, idx))

    kv_data['ISS log'] = iss_log
    kv_data['ISS csv'] = iss_csv
    try:
        if iss == "spike":
            process_spike_sim_log(iss_log, iss_csv)
        else:
            assert iss == 'ovpsim'  # (should be checked by argparse)
            process_ovpsim_sim_log(iss_log, iss_csv)
    except (OSError, RuntimeError) as e:
        return (False, f'ISS log processing failed ({e})', kv_data)

    compare_log = os.path.join(rtl_log_dir, 'compare.log')
    kv_data['comparison log'] = compare_log

    # Delete any existing file at compare_log (the compare_trace_csv function
    # would append to it, which is rather confusing).
    try:
        os.remove(compare_log)
    except FileNotFoundError:
        pass

    compare_result = \
        compare_trace_csv(rtl_csv, iss_csv, "ibex", iss, compare_log,
                          **test.get('compare_opts', {}))

    # Rather oddly, compare_result is a string. The comparison passed if it
    # starts with '[PASSED]' and failed otherwise.
    compare_passed = compare_result.startswith('[PASSED]: ')
    if not compare_passed:
        assert compare_result.startswith('[FAILED]: ')
        # compare_result[10:] will look like "123 matched, 321 mismatch",
        # meaning that 123 instructions matched and 321 instructions didn't.
        kv_data['compared instructions'] = compare_result[10:]
        return (False, 'mismatch between ISS and RTL', kv_data)

    # compare_result[10:] will look like "123 matched", meaning that 123
    # instructions matched.
    kv_data['compared instructions'] = compare_result[10:]
    return (True, None, kv_data)


def on_result(result: _CompareResult, output: TextIO) -> None:
    passed, err_msg, kv_data = result

    if passed:
        assert err_msg is None
        output.write('PASS\n\n')
    else:
        assert err_msg is not None
        output.write('FAIL\n\n')
        output.write(f'Test failed: {err_msg}\n')
        output.write('---\n\n')

    klen = 1
    for k in kv_data:
        klen = max(klen, len(k))

    for k, v in kv_data.items():
        kpad = ' ' * (klen - len(k))
        output.write(f'{k}:{kpad} | {v}\n')


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--iss', required=True, choices=['spike', 'ovpsim'])
    parser.add_argument('--iss-log-dir', required=True)
    parser.add_argument('--start-seed', type=int, required=True)
    parser.add_argument('--test-dot-seed',
                        type=read_test_dot_seed,
                        required=True)
    parser.add_argument('--rtl-log-dir', required=True)
    parser.add_argument('--output', required=True)

    args = parser.parse_args()
    if args.start_seed < 0:
        raise RuntimeError('Invalid start seed: {}'.format(args.start_seed))

    testname, seed = args.test_dot_seed
    if seed < args.start_seed:
        raise RuntimeError('Start seed is greater than test seed '
                           f'({args.start_seed} > {seed}).')

    iteration = seed - args.start_seed

    entry = get_test_entry(testname)

    result = compare_test_run(entry, iteration, seed,
                              args.rtl_log_dir, args.iss, args.iss_log_dir)
    with open(args.output, 'w', encoding='UTF-8') as outfile:
        on_result(result, outfile)

    # Always return 0 (success), even if the test failed. We've successfully
    # generated a comparison log either way and we don't want to stop Make from
    # gathering them all up for us.
    return 0


if __name__ == '__main__':
    sys.exit(main())
