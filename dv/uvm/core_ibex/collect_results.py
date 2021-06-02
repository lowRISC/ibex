#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys


def parse_log(path: str) -> bool:
    first_line = '(empty file)'
    with open(path, 'r', encoding='UTF-8') as log:
        for line in log:
            first_line = line.rstrip()
            break

    if first_line == 'PASS':
        return True
    if first_line.startswith('FAIL'):
        return False

    raise RuntimeError('Strange first line ({!r})'.format(first_line))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', '-o', required=True)
    parser.add_argument('log', nargs='*')

    args = parser.parse_args()

    fail_count = 0
    pass_count = 0
    for log_path in args.log:
        try:
            passed = parse_log(log_path)
        except RuntimeError as e:
            print(f'Failed to parse run results at {log_path:!r}: {e}',
                  file=sys.stderr)
            passed = False

        if passed:
            pass_count += 1
        else:
            fail_count += 1

    msg = '{} PASSED, {} FAILED'.format(pass_count, fail_count)
    with open(args.output, 'w', encoding='UTF-8') as outfile:
        print(msg, file=outfile)
    print(msg)

    # Succeed if no tests failed
    return 1 if fail_count else 0


if __name__ == '__main__':
    sys.exit(main())
