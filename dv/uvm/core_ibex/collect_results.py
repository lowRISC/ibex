#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import argparse
import sys
from typing import TextIO


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


def dump_log(path: str, dest: TextIO) -> None:
    print('\nLog at {}:'.format(path), file=dest)
    with open(path, 'r') as fd:
        for line in fd:
            dest.write('> ' + line)


def box_comment(line: str) -> str:
    hr = '#' * 80
    return hr + '\n# ' + line + '\n' + hr


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', '-o', required=True)
    parser.add_argument('log', nargs='*')

    args = parser.parse_args()

    bad_logs = []
    good_logs = []
    for log_path in args.log:
        try:
            passed = parse_log(log_path)
        except RuntimeError as e:
            print(f'Failed to parse run results at {log_path:!r}: {e}',
                  file=sys.stderr)
            passed = False

        if passed:
            good_logs.append(log_path)
        else:
            bad_logs.append(log_path)

    msg = '{} PASSED, {} FAILED'.format(len(good_logs), len(bad_logs))
    with open(args.output, 'w', encoding='UTF-8') as outfile:
        print(msg, file=outfile)
        if bad_logs:
            print('\n\n' + box_comment('Details of failing tests'),
                  file=outfile)
            for log_path in bad_logs:
                dump_log(log_path, outfile)

        if good_logs:
            print('\n\n' + box_comment('Details of passing tests'),
                  file=outfile)
            for log_path in good_logs:
                dump_log(log_path, outfile)

    print(msg)

    # Succeed if no tests failed
    return 1 if bad_logs else 0


if __name__ == '__main__':
    sys.exit(main())
