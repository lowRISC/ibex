#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import os
import sys


_CORE_IBEX = os.path.normpath(os.path.join(os.path.dirname(__file__)))
_IBEX_ROOT = os.path.normpath(os.path.join(_CORE_IBEX, '../../..'))
_RISCV_DV_ROOT = os.path.join(_IBEX_ROOT, 'vendor/google_riscv-dv')
_OLD_SYS_PATH = sys.path


def main() -> int:
    """
    Construct a trivial makefile from the --debug output of riscv-dv commands.

    Creates a flat makefile, so if the commands have any ordering requirements
    this will fall over.
    """
    parser = argparse.ArgumentParser()
    parser.add_argument('--test_cmds', required=True,
                        help='File containing --debug output')
    parser.add_argument('--output', required=True,
                        help='Makefile to be constructed')
    parser.add_argument("--discard_stdstreams", action='store_true',
                        help='Redirect stdstreams to /dev/null')
    args = parser.parse_args()

    # Many commands come with a logfile argument, however some capture the
    # stdout/stderr to a file. Handle both cases to ensure the logs are tidy.
    tail = '\n'
    if args.discard_stdstreams:
        tail = ' >/dev/null 2>&1' + tail

    with open(args.test_cmds) as f, \
         open(args.output, 'w', encoding='UTF-8') as outfile:
        for i, line in enumerate(f):
            outfile.write(f'{i}:\n')
            outfile.write('\t' + line.strip() + tail)
        outfile.write(f'CMDS := $(shell seq 0 {i})\n')
        outfile.write('all: $(CMDS)')

    return 0


if __name__ == '__main__':
    sys.exit(main())
