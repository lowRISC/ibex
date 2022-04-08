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
    parser = argparse.ArgumentParser()
    parser.add_argument('--test_cmds', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()

    with open(args.test_cmds) as f, \
         open(args.output, 'w', encoding='UTF-8') as outfile:
        for i, line in enumerate(f):
            outfile.write(f'{i}:\n')
            outfile.write('\t' + line)
        outfile.write(f'CMDS := $(shell seq 0 {i})\n')
        outfile.write('all: $(CMDS)')

    return 0


if __name__ == '__main__':
    sys.exit(main())
