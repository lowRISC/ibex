#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys

from scripts_lib import run_one, subst_vars
from sim_cmd import get_simulator_cmd


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')

    parser.add_argument('--output', required=True)
    parser.add_argument('--simulator', required=True)
    parser.add_argument('--en_cov', action='store_true')
    parser.add_argument('--en_wave', action='store_true')
    parser.add_argument('--en_cosim', action='store_true')
    parser.add_argument('--compile-opts', default='')

    args = parser.parse_args()

    output_dir = os.path.join(args.output, 'rtl_sim')
    os.makedirs(output_dir, exist_ok=True)

    enables = {
        'cov_opts': args.en_cov,
        'wave_opts': args.en_wave,
        'cosim_opts': args.en_cosim
    }
    compile_cmds, _ = get_simulator_cmd(args.simulator, enables)

    for pre_cmd in compile_cmds:
        cmd = subst_vars(pre_cmd,
                         {
                             'out': output_dir,
                             'cmp_opts': args.compile_opts
                         })
        retcode = run_one(args.verbose, ['sh', '-c', cmd],
                          redirect_stdstreams='/dev/null')
        if retcode:
            return retcode

    return 0


if __name__ == '__main__':
    sys.exit(main())
