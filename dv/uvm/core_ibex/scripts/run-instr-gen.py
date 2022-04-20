#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import re
import shlex
import shutil
import sys
import tempfile
from typing import List

from scripts_lib import read_test_dot_seed, start_riscv_dv_run_cmd, run_one


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--simulator', required=True)
    parser.add_argument('--end-signature-addr', required=True)
    parser.add_argument('--output-dir', required=True)
    parser.add_argument('--gen-build-dir', required=True)
    parser.add_argument('--isa', required=True)

    parser.add_argument('--test-dot-seed',
                        type=read_test_dot_seed, required=True)

    parser.add_argument('--pmp-num-regions', type=int, required=True)
    parser.add_argument('--pmp-granularity', type=int, required=True)

    args = parser.parse_args()

    testname, seed = args.test_dot_seed

    inst_overrides = [
        'riscv_asm_program_gen',
        'ibex_asm_program_gen',
        'uvm_test_top.asm_gen'
    ]
    sim_opts_dict = {
        'uvm_set_inst_override': ','.join(inst_overrides),
        'signature_addr': args.end_signature_addr,
        'pmp_num_regions': str(args.pmp_num_regions),
        'pmp_granularity': str(args.pmp_granularity),
        'tvec_alignment': '8'
    }
    sim_opts_str = ' '.join('+{}={}'.format(k, v)
                            for k, v in sim_opts_dict.items())

    output_pfx = os.path.join(args.output_dir, f'{testname}.{seed}')

    riscv_dv_log = output_pfx + '.riscv-dv.log'
    gen_log = output_pfx + '.gen.log'
    gen_asm = output_pfx + '.S'

    # Ensure that the output directory actually exists
    os.makedirs(args.output_dir, exist_ok=True)

    with tempfile.TemporaryDirectory() as td:
        orig_list = os.path.join(td, 'cmds.list')

        placeholder = os.path.join(td, '@@PLACEHOLDER@@')

        cmd = (start_riscv_dv_run_cmd(args.verbose) +
               ['--so', '--steps=gen',
                '--output', placeholder,
                '--simulator', args.simulator,
                '--isa', args.isa,
                '--test', testname,
                '--start_seed', str(seed),
                '--iterations', '1',
                '--sim_opts', sim_opts_str,
                '--debug', orig_list])

        # Run riscv-dv to generate commands. This is rather chatty, so redirect
        # its output to a log file.
        gen_retcode = run_one(args.verbose, cmd,
                              redirect_stdstreams=riscv_dv_log)
        if gen_retcode:
            return gen_retcode

        # Those commands assume the riscv-dv directory layout, where the build
        # and run directories are the same. Transform each of the commands as
        # necessary to point at the built generator
        cmds = reloc_commands(placeholder,
                              args.gen_build_dir,
                              td,
                              args.simulator,
                              testname,
                              orig_list)

        # Run the commands in sequence to create "test_0.S" and "gen.log" in
        # the temporary directory.
        ret = 0
        for cmd in cmds:
            ret = run_one(args.verbose, cmd, redirect_stdstreams='/dev/null')
            if ret != 0:
                break

        td_gen_log = os.path.join(td, 'gen.log')
        td_gen_asm = os.path.join(td, 'test_0.S')

        # At this point, we might have a "gen.log" in the temporary directory.
        # Copy it back if so. If not, check that ret is nonzero.
        if os.path.exists(td_gen_log):
            shutil.copy(td_gen_log, gen_log)
        elif ret == 0:
            raise RuntimeError('Generation commands exited with zero status '
                               'but left no gen.log in scratch directory.')

        # If we failed, exit now (rather than copying the .S file across)
        if ret != 0:
            return ret

        # We succeeded. Check there is indeed a test_0.S in the temporary
        # directory and copy it back.
        if not os.path.exists(td_gen_asm):
            raise RuntimeError('Generation commands exited with zero status '
                               'but left no test_0.S in scratch directory.')

        shutil.copy(td_gen_asm, gen_asm)

    return 0


def reloc_commands(placeholder_dir: str,
                   build_dir: str,
                   scratch_dir: str,
                   simulator: str,
                   testname: str,
                   src: str) -> List[List[str]]:
    '''Reads the (one) line in src and apply relocations to it

    The result should be a series of commands that build a single test into
    scratch_dir/test_0.S, dumping a log into scratch_dir/gen.log.

    '''
    ret = []
    with open(src) as src_file:
        for line in src_file:
            line = line.strip()
            if not line:
                continue

            ret.append([reloc_word(simulator,
                                   placeholder_dir, build_dir,
                                   scratch_dir, testname, w)
                        for w in shlex.split(line)])
    return ret


def reloc_word(simulator: str,
               placeholder_dir: str, build_dir: str, scratch_dir: str,
               testname: str, word: str) -> str:
    '''Helper function for reloc_commands that relocates just one word'''
    sim_relocs = {
        'vcs': [
            # The VCS-generated binary
            (os.path.join(placeholder_dir, 'vcs_simv'),
             os.path.join(build_dir, 'vcs_simv'))
        ],
        'xlm': [
            # For Xcelium, the build directory gets passed as the
            # "-xmlibdirpath" argument.
            (placeholder_dir, build_dir)
        ]
    }
    always_relocs = [
        # The generated test. Since riscv-dv expects to make more than one of
        # them, this gets supplied as a plusarg with just the test name (with
        # no seed suffix).
        (os.path.join(placeholder_dir, 'asm_test', testname),
         os.path.join(scratch_dir, 'test')),

        # The log file for generation itself
        (os.path.join(placeholder_dir, f'sim_{testname}_0.log'),
         os.path.join(scratch_dir, 'gen.log'))
    ]

    # Special handling for plusargs with filenames, which end up looking
    # something like +my_argument=foo/bar/baz.
    match = re.match(r'(\+[A-Za-z0-9_]+=)(.*)', word)
    if match is not None:
        pre = match.group(1)
        post = match.group(2)
    else:
        pre = ''
        post = word

    abs_post = os.path.abspath(post)

    for orig, reloc in sim_relocs[simulator] + always_relocs:
        abs_orig = os.path.abspath(orig)
        if abs_orig == abs_post:
            post = reloc
            break

    reloc = pre + post

    # Check there's no remaining occurrence of the placeholder
    if placeholder_dir in reloc:
        raise RuntimeError('Failed to replace an occurrence of the '
                           f'placeholder in {word} (got {reloc})')

    return reloc


if __name__ == '__main__':
    sys.exit(main())
