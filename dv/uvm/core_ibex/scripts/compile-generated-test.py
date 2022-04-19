#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import shlex
import sys
import tempfile

from scripts_lib import read_test_dot_seed, start_riscv_dv_run_cmd, run_one


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--output', required=True)
    parser.add_argument('--isa', required=True)

    parser.add_argument('--input-dir', required=True)
    parser.add_argument('--test-dot-seed',
                        type=read_test_dot_seed, required=True)
    parser.add_argument('--start-seed', type=int, required=True)

    args = parser.parse_args()

    if args.start_seed < 0:
        raise RuntimeError('Invalid start seed: {}'.format(args.start_seed))
    testname, seed = args.test_dot_seed
    if seed < args.start_seed:
        raise RuntimeError('Start seed is greater than test seed '
                           f'({args.start_seed} > {seed}).')

    iteration = seed - args.start_seed

    if not args.output.endswith('.bin'):
        raise RuntimeError("Output argument must end with .bin: "
                           f"got {args.output!r}")
    out_base = args.output[:-4]
    out_riscv_dv_path = out_base + '.riscv-dv.log'
    out_obj_path = out_base + '.o'

    src_file = os.path.join(args.input_dir, f'{testname}_{iteration}.S')
    if not os.path.exists(src_file):
        raise RuntimeError(f'No such input file: {src_file!r}.')

    # Run riscv-dv to get a list of commands that it would run to try to
    # compile and convert the files in question. These will need some massaging
    # to match our paths, but we can't generate the commands by hand because
    # there are several test-specific options that might appear.
    with tempfile.TemporaryDirectory() as td:
        placeholder = os.path.join(td, '@@PLACEHOLDER@@')
        orig_list = os.path.join(td, 'orig-cmds.list')

        dv_ret = run_one(False,
                         start_riscv_dv_run_cmd(args.verbose) +
                         ['--verbose',
                          '--output', placeholder,
                          '--steps=gcc_compile',
                          '--test', testname,
                          '--start_seed', str(seed),
                          '--iterations', '1',
                          '--isa', args.isa,
                          '--debug', orig_list],
                         redirect_stdstreams=out_riscv_dv_path)
        if dv_ret:
            return dv_ret

        orig_cmds = []
        with open(orig_list) as orig_file:
            for line in orig_file:
                line = line.strip()
                if not line:
                    continue
                orig_cmds.append(shlex.split(line))

    # Do the massaging. We intentionally used "@@PLACEHOLDER@@" as a path in
    # our call to riscv-dv, which should let us find all the things that matter
    # easily.
    rewrites = [
        (f"{placeholder}/asm_test/{testname}_0.S", src_file),
        (f"{placeholder}/asm_test/{testname}_0.o", out_obj_path),
        (f"{placeholder}/asm_test/{testname}_0.bin", args.output)
    ]
    new_cmds = []
    for cmd in orig_cmds:
        new_cmd = []
        for word in cmd:
            for old, new in rewrites:
                word = word.replace(old, new)

            if placeholder in word:
                raise RuntimeError("Couldn't replace every copy of "
                                   f"placeholder in {cmd}")

            new_cmd.append(word)
        new_cmds.append(new_cmd)

    # Finally, run all the commands
    for cmd in new_cmds:
        ret = run_one(args.verbose, cmd)
        if ret != 0:
            return ret


if __name__ == '__main__':
    sys.exit(main())
