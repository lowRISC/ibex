#!/usr/bin/env python3
"""Run RTL simulation for a Snippy-produced external payload.

This is a Snippy-specific companion to run_rtl.py.

The standard Ibex run_rtl.py entry point expects a TestRunResult object created
by the normal Ibex regression flow and selected through --test-dot-seed. The
Snippy flow prepares its payload outside that model:

  riscv-dv asm + llvm-snippy ELF -> linked ELF -> elf_manifest.svload

This script accepts those already-prepared artifacts directly, but still uses
the standard Ibex simulator abstraction through rtl_simulation.yaml.

Additionally, it exports a standard Ibex TestRunResult-compatible record for
the Snippy run. This lets later Ibex Make goals discover Snippy results as
ordinary regression artifacts.
"""

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import fcntl
import json
import re
import shutil
import subprocess
import sys
from typing import List, Optional

import pathlib3x as pathlib

from ibex_cmd import get_sim_opts
import riscvdv_interface
from metadata import RegressionMetadata
from scripts_lib import run_one, format_to_cmd
from test_run_result import TestRunResult, TestType, Failure_Modes

import logging
logger = logging.getLogger(__name__)


_SNIPPY_AUTO_SEED_RE = re.compile(
    r'no instructions seed specified, using auto-generated one:\s*([0-9]+)'
)


def _existing_path(path: pathlib.Path, what: str) -> pathlib.Path:
    if not path.exists():
        raise RuntimeError(f'{what} does not exist: {path}')
    return path


def _read_snippy_seed(snippy_log: pathlib.Path) -> int:
    _existing_path(snippy_log, 'Snippy log')

    for line in snippy_log.read_text(errors='replace').splitlines():
        match = _SNIPPY_AUTO_SEED_RE.search(line)
        if match:
            return int(match.group(1))

    raise RuntimeError(
        f'Could not find Snippy auto-generated seed in {snippy_log}'
    )


def _generate_rtl_trace_csv(md: RegressionMetadata,
                            trace_log: pathlib.Path,
                            output_csv: pathlib.Path) -> None:
    """Convert an Ibex RTL trace log into riscv-dv CSV trace format.

    This reuses the existing Snippy-specific converter that used to be called
    from the CMake functional coverage artifact collection path.
    """

    _existing_path(trace_log, 'RTL trace log')

    output_csv.parent.mkdir(exist_ok=True, parents=True)

    converter_dir = md.ibex_dv_root / 'riscv_dv_extension'
    scripts_dir = md.ibex_dv_root / 'scripts'

    sys.path.insert(0, str(scripts_dir))
    sys.path.insert(0, str(converter_dir))

    try:
        from snippy_ibex_log_to_trace_csv import process_ibex_sim_log
    except ImportError as err:
        raise RuntimeError(
            f'Failed to import snippy_ibex_log_to_trace_csv from '
            f'{converter_dir}'
        ) from err

    process_ibex_sim_log(str(trace_log), str(output_csv))

    if not output_csv.exists():
        raise RuntimeError(f'RTL trace CSV was not generated: {output_csv}')


def _refresh_analysis_log_link(src: pathlib.Path,
                               analysis_log: Optional[pathlib.Path]) -> None:
    """Expose the standard stdstreams log at a CMake-known path.

    This is kept only for backwards compatibility. The cleaned CMake flow should
    prefer --run-info-json and should not pass --analysis-log.
    """

    if analysis_log is None:
        return

    analysis_log.parent.mkdir(exist_ok=True, parents=True)

    if analysis_log.exists() or analysis_log.is_symlink():
        analysis_log.unlink()

    try:
        analysis_log.symlink_to(src)
    except OSError:
        shutil.copy2(src, analysis_log)


def _write_snippy_result(result_json: Optional[pathlib.Path],
                         test_name: str,
                         iteration: int,
                         snippy_seed: int,
                         std_test_dir: pathlib.Path,
                         std_rtl_stdout: pathlib.Path) -> None:
    """Write the minimal CMake-side Snippy run result.

    The analyzer updates this file later by adding the final PASS/FAIL status.
    Runtime artifacts themselves remain in the standard Ibex run directory.
    """

    if result_json is None:
        return

    result_json.parent.mkdir(exist_ok=True, parents=True)

    data = {
        "layout": test_name,
        "iteration": iteration,
        "snippy_seed": snippy_seed,
        "test_run_dir": str(std_test_dir),
        "log_file": str(std_rtl_stdout),
    }

    tmp_path = result_json.with_suffix(result_json.suffix + ".tmp")
    tmp_path.write_text(json.dumps(data, indent=2) + "\n")
    tmp_path.replace(result_json)


def _append_snippy_make_entry(md: RegressionMetadata, testdotseed: str) -> None:
    """Register this Snippy run as a standard Ibex comp-result.

    The file is included by ibex_sim.mk on later Make invocations. Since Snippy
    runs can happen in parallel, protect the read/modify/write sequence with
    flock.
    """

    snippy_tests_mk = md.dir_metadata / 'snippy_tests.mk'
    snippy_tests_mk.parent.mkdir(exist_ok=True, parents=True)

    entry_lines = [
        f'snippy-testdots += {testdotseed}\n',
        f'comp-results += $(TESTS-DIR)/{testdotseed}/trr.yaml\n',
    ]

    with open(snippy_tests_mk, 'a+') as fd:
        fcntl.flock(fd, fcntl.LOCK_EX)

        fd.seek(0)
        existing = fd.read()

        for line in entry_lines:
            if line not in existing:
                fd.write(line)

        fd.flush()
        fcntl.flock(fd, fcntl.LOCK_UN)


def _make_test_run_result(md: RegressionMetadata,
                          testdotseed: str,
                          test_name: str,
                          snippy_seed: int,
                          timeout_s: int,
                          rtl_test: str,
                          linked_elf: pathlib.Path,
                          elf_layout: pathlib.Path,
                          std_test_dir: pathlib.Path,
                          std_rtl_log: pathlib.Path,
                          std_rtl_stdout: pathlib.Path,
                          std_rtl_trace: pathlib.Path,
                          std_iss_cosim_trace: pathlib.Path,
                          rtl_cmds: List[List[str]],
                          failure_mode,
                          failure_message) -> None:
    trr = TestRunResult(
        passed=None,
        failure_mode=failure_mode,
        failure_message=failure_message,
        timeout_s=timeout_s,
        testtype=TestType.DIRECTED,
        testdotseed=testdotseed,
        testname=f'snippy_{test_name}',
        seed=snippy_seed,

        # Snippy/ELF-manifest tests do not use the raw +bin flow. Keep the
        # linked ELF here for traceability: it is the artifact from which the
        # .svload manifest was generated.
        binary=linked_elf,

        rtl_simulator=md.simulator,
        iss_cosim=md.iss,
        rtl_test=[rtl_test],
        sim_opts=[f'+elf_manifest={elf_layout}'],
        dir_test=std_test_dir,
        rtl_log=std_rtl_log,
        rtl_stdout=std_rtl_stdout,
        rtl_trace=std_rtl_trace,
        iss_cosim_trace=std_iss_cosim_trace,
        dir_fcov=md.dir_fcov / 'tests' / testdotseed,
        rtl_cmds=rtl_cmds,
        metadata_pickle_file=md.pickle_file,
        pickle_file=md.dir_metadata / f'{testdotseed}.pickle',
        yaml_file=std_test_dir / 'trr.yaml',
    )

    trr.export(write_yaml=True)
    _append_snippy_make_entry(md, testdotseed)


def _main() -> int:
    parser = argparse.ArgumentParser(
        description='Run RTL simulation for a Snippy-generated Ibex payload.'
    )

    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)

    parser.add_argument('--test-name', type=str, required=True,
                        help='Name used for reporting and coverage test naming.')
    parser.add_argument('--iteration', type=int, required=True,
                        help='CMake iteration index used for reporting.')
    parser.add_argument('--result-json', type=pathlib.Path, required=True,
                        help='CMake-side per-run result JSON path.')
    parser.add_argument('--seed', type=int, required=True,
                        help='Fallback seed passed to the RTL simulator backend.')

    parser.add_argument('--linked-elf', type=pathlib.Path, required=True,
                        help='Linked ELF used to generate the ELF layout. '
                             'Stored in metadata for traceability.')
    parser.add_argument('--elf-layout', '--elf-manifest',
                        dest='elf_layout',
                        type=pathlib.Path,
                        required=True,
                        help='Snippy ELF layout .svload consumed by the custom '
                             'RTL test. --elf-manifest is kept as a deprecated '
                             'alias for older callers.')
    parser.add_argument('--snippy-log', type=pathlib.Path, required=True,
                        help='Snippy generation log containing the Snippy seed.')

    parser.add_argument('--rtl-test', type=str, required=True,
                        help='UVM test name passed as <rtl_test>.')

    parser.add_argument('--timeout-s', type=int, required=True,
                        help='Timeout passed to the testbench and subprocess watchdog.')
    parser.add_argument('--signature-addr', type=str, required=True,
                        help='Signature address passed to the testbench.')

    parser.add_argument('--extra-sim-opts', type=str, action='append', default=[],
                        help='Extra simulator plusargs/options appended to <sim_opts>.')

    args = parser.parse_args()

    md = RegressionMetadata.construct_from_metadata_dir(args.dir_metadata)

    _existing_path(args.linked_elf, 'Snippy linked ELF')
    _existing_path(args.elf_layout, 'Snippy ELF layout')
    _existing_path(args.snippy_log, 'Snippy log')

    snippy_seed = _read_snippy_seed(args.snippy_log)
    testdotseed = f'snippy_{args.test_name}.{snippy_seed}'

    std_test_dir = md.dir_tests / testdotseed
    std_test_dir.mkdir(exist_ok=True, parents=True)

    std_rtl_log = std_test_dir / 'rtl_sim.log'
    std_rtl_stdout = std_test_dir / 'rtl_sim_stdstreams.log'
    std_rtl_trace_base = std_test_dir / 'trace_core'
    std_rtl_trace = std_test_dir / 'trace_core_00000000.log'
    std_rtl_trace_csv = std_test_dir / 'rtl_trace.csv'
    std_iss_cosim_trace = (
        std_test_dir / f'{md.iss}_cosim_trace_core_00000000.log'
    )

    extra_sim_opts = ''
    if args.extra_sim_opts:
        extra_sim_opts = '\n'.join(args.extra_sim_opts) + '\n'

    snippy_sim_opts = (
        f"+signature_addr={args.signature_addr}\n"
        f"+test_timeout_s={args.timeout_s}\n"
        f"+elf_manifest={args.elf_layout}\n"
        f"{get_sim_opts(md.ibex_config, md.simulator, md.rv32zc)}\n"
        f"{extra_sim_opts}"
    )

    subst_vars_dict = {
        'cwd': md.ibex_root,
        'test_name': testdotseed,
        'rtl_test': args.rtl_test,
        'seed': str(snippy_seed),

        # The Snippy flow uses +elf_manifest instead of +bin. Keep this empty
        # for simulator YAML templates that still substitute <binary>.
        'binary': '',

        'test_dir': std_test_dir,
        'tb_dir': md.dir_tb,
        'dir_shared_cov': md.dir_shared_cov,
        'rtl_sim_log': std_rtl_log,
        'rtl_trace': std_rtl_trace_base,
        'iss_cosim_trace': std_iss_cosim_trace,
        'core_ibex': md.ibex_dv_root,
        'sim_opts': snippy_sim_opts,
    }

    sim_cmds = riscvdv_interface.get_tool_cmds(
        yaml_path=md.ibex_riscvdv_simulator_yaml,
        simulator=md.simulator,
        cmd_type='sim',
        user_enables={
            'cov_opts': md.cov,
            'wave_opts': md.waves,
        },
        user_subst_options=subst_vars_dict)

    rtl_cmds = [format_to_cmd(cmd) for cmd in sim_cmds]
    logger.info(rtl_cmds)

    failure_mode = None
    failure_message = None

    with open(std_rtl_stdout, 'wb') as sim_fd:
        try:
            for cmd in rtl_cmds:
                sim_fd.write(
                    f"Running Snippy RTL command:\n{' '.join(cmd)}\n".encode()
                )
                run_one(md.verbose,
                        cmd,
                        redirect_stdstreams=sim_fd,
                        timeout_s=args.timeout_s + 60,
                        reraise=True)
        except subprocess.TimeoutExpired:
            failure_mode = Failure_Modes.TIMEOUT
            failure_message = (
                "[FAILURE] Simulation process killed due to timeout "
                f"[{args.timeout_s + 60}s].\n"
            )
            sim_fd.write(failure_message.encode())

    _existing_path(std_rtl_log, 'RTL simulation log')
    _existing_path(std_rtl_trace, 'RTL trace log')
    _existing_path(std_iss_cosim_trace, 'ISS cosim trace')

    _generate_rtl_trace_csv(md, std_rtl_trace, std_rtl_trace_csv)

    _make_test_run_result(md,
                          testdotseed,
                          args.test_name,
                          snippy_seed,
                          args.timeout_s,
                          args.rtl_test,
                          args.linked_elf,
                          args.elf_layout,
                          std_test_dir,
                          std_rtl_log,
                          std_rtl_stdout,
                          std_rtl_trace,
                          std_iss_cosim_trace,
                          rtl_cmds,
                          failure_mode,
                          failure_message)

    _write_snippy_result(args.result_json,
                         args.test_name,
                         args.iteration,
                         snippy_seed,
                         std_test_dir,
                         std_rtl_stdout)

    return 0


if __name__ == '__main__':
    try:
        sys.exit(_main())
    except RuntimeError as err:
        sys.stderr.write(f'Error: {err}\n')
        sys.exit(1)
