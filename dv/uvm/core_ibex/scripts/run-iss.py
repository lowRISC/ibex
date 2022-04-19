#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys

from scripts_lib import read_test_dot_seed, run_one


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    parser.add_argument('--iss', required=True)
    parser.add_argument('--test-dot-seed',
                        type=read_test_dot_seed, required=True)
    parser.add_argument('--gen-dir', required=True)
    parser.add_argument('--run-dir', required=True)
    parser.add_argument('--isa', required=True)

    parser.add_argument('--start-seed', type=int, required=True)

    args = parser.parse_args()

    testname, seed = args.test_dot_seed

    if args.start_seed < 0:
        raise RuntimeError('Invalid start seed: {}'.format(args.start_seed))
    testname, seed = args.test_dot_seed
    if seed < args.start_seed:
        raise RuntimeError('Start seed is greater than test seed '
                           f'({args.start_seed} > {seed}).')

    iteration = seed - args.start_seed

    # riscv-dv knows how to run an ISS simulation (see yaml/iss.yaml in the
    # vendored directory), but it has definite (and inconvenient!) opinions
    # about where files should end up. Rather than fight with it, let's just
    # generate the simple ISS command ourselves.
    #
    # NOTE: This only supports Spike, mainly because it's the only simulator we
    # care about at the moment and this whole script is going to go away anyway
    # very soon once we've switched across to using cosimulation.

    if args.iss != 'spike':
        raise RuntimeError(f'Unsupported ISS: {args.iss}')

    object_name = f'{testname}_{iteration}.o'
    log_name = os.path.join(args.run_dir, f'{testname}.{seed}.log')

    spike_dir = os.getenv('SPIKE_PATH')
    if spike_dir is not None:
        spike = os.path.join(spike_dir, 'spike')
    else:
        spike = 'spike'

    cmd = [spike, '--log-commits',
           '--isa', args.isa,
           '-l', os.path.join(args.gen_dir, 'asm_test', object_name)]
    return run_one(args.verbose,
                   cmd,
                   redirect_stdstreams=log_name)


if __name__ == '__main__':
    sys.exit(main())
