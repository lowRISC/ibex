#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys

from ibex_cmd import get_compile_opts
from scripts_lib import THIS_DIR, run_one, subst_vars
from sim_cmd import get_simulator_cmd


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')

    parser.add_argument('--ibex-config', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--simulator', required=True)
    parser.add_argument('--en_cov', action='store_true')
    parser.add_argument('--en_wave', action='store_true')
    parser.add_argument('--en_cosim', action='store_true')

    args = parser.parse_args()

    expected_env_vars = ['PRJ_DIR', 'LOWRISC_IP_DIR']
    for var in expected_env_vars:
        if os.getenv(var) is None:
            raise RuntimeError(f'The environment variable {var!r} is not set.')

    core_ibex = os.path.normpath(os.path.join(THIS_DIR, '..'))

    os.makedirs(args.output, exist_ok=True)

    enables = {
        'cov_opts': args.en_cov,
        'wave_opts': args.en_wave,
        'cosim_opts': args.en_cosim
    }
    compile_cmds, _ = get_simulator_cmd(args.simulator, enables)

    for pre_cmd in compile_cmds:
        cmd = subst_vars(pre_cmd,
                         {
                             'core_ibex': core_ibex,
                             'out': args.output,
                             'cmp_opts': get_compile_opts(args.ibex_config,
                                                          args.simulator)
                         })
        retcode = run_one(args.verbose, ['sh', '-c', cmd],
                          redirect_stdstreams='/dev/null')
        if retcode:
            return retcode

    return 0


if __name__ == '__main__':
    sys.exit(main())
