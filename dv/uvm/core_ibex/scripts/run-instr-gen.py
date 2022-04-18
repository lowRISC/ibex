#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import shlex
import sys
import tempfile

import construct_makefile
from scripts_lib import start_riscv_dv_run_cmd, run_one


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--simulator', required=True)
    parser.add_argument('--end-signature-addr', required=True)
    parser.add_argument('--gen-build-dir', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--isa', required=True)

    parser.add_argument('--test', required=True)
    parser.add_argument('--start-seed', type=int, required=True)
    parser.add_argument('--iterations', type=int, required=True)

    parser.add_argument('--pmp-num-regions', type=int, required=True)
    parser.add_argument('--pmp-granularity', type=int, required=True)

    args = parser.parse_args()

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

    output_makefile = os.path.join(args.output, 'run.mk')

    with tempfile.TemporaryDirectory() as td:
        orig_list = os.path.join(td, 'orig-cmds.list')
        reloc_list = os.path.join(td, 'reloc-cmds.list')

        cmd = (start_riscv_dv_run_cmd(args.verbose) +
               ['--so', '--steps=gen',
                '--output', args.output,
                '--simulator', args.simulator,
                '--isa', args.isa,
                '--test', args.test,
                '--start_seed', str(args.start_seed),
                '--iterations', str(args.iterations),
                '--sim_opts', sim_opts_str,
                '--debug', orig_list])

        # Run riscv-dv to generate a bunch of commands
        gen_retcode = run_one(args.verbose, cmd)
        if gen_retcode:
            return gen_retcode

        # Those commands assume the riscv-dv directory layout, where the build
        # and run directories are the same. Transform each of the commands as
        # necessary to point at the built generator
        reloc_commands(args.simulator, args.output, args.gen_build_dir,
                       orig_list, reloc_list)

        # Convert the final command list to a Makefile
        construct_makefile.transform(True, reloc_list, output_makefile)

    # Finally, run Make to run those commands
    cmd = ['make', '-f', output_makefile, 'all']
    if not args.verbose:
        cmd.append('-s')

    return run_one(args.verbose, cmd)


def reloc_commands(simulator: str, run_dir: str, build_dir: str,
                   src: str, dst: str) -> None:
    '''Reads all the lines in src and "relocate" them to dst.

    More precisely, try to find paths in these lines that refer to things that
    were actually built as part of the build step (compiling the instruction
    generator) and switch those paths over to point at the correct directory.

    '''
    with open(src) as src_file, open(dst, 'w') as dst_file:
        for line in src_file:
            line = line.strip()
            if not line:
                continue

            parts = shlex.split(line)
            reloc_parts = [reloc_word(simulator, run_dir, build_dir, w)
                           for w in parts]
            reloc_line = ' '.join([shlex.quote(w) for w in reloc_parts])
            print(reloc_line, file=dst_file)


def reloc_word(simulator: str, run_dir: str, build_dir: str, word: str) -> str:
    '''Helper function for reloc_commands that relocates just one word

    This is a bit of a hack, made necessary because riscv-dv doesn't really
    support building the instruction generator in a different directory from
    where we run it.

    '''
    reloc_basenames = {
        'vcs': [
            # The VCS binary
            'vcs_simv'
        ],
        'xlm': [
            # For Xcelium, the build directory gets passed as the
            # "-xmlibdirpath" argument. The basename there will be "instr_gen".
            'instr_gen'
        ]
    }

    basename = os.path.basename(word)
    if basename not in reloc_basenames[simulator]:
        # This doesn't look like a file we care about tracking
        return word

    abs_word = os.path.abspath(word)
    abs_rundir = os.path.abspath(run_dir)

    common_path = os.path.commonpath([abs_word, abs_rundir])
    if common_path != abs_rundir:
        # The file wasn't in the run_dir tree.
        return word

    # Avoid a path like "a/b/c/." if abs_word happens to equal abs_rundir
    if abs_word == abs_rundir:
        return build_dir

    rel_word = os.path.relpath(abs_word, abs_rundir)
    return os.path.join(build_dir, rel_word)


if __name__ == '__main__':
    sys.exit(main())
