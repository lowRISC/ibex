#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import shlex
import subprocess
import sys
from typing import List

THIS_DIR = os.path.dirname(__file__)
IBEX_ROOT = os.path.join(THIS_DIR, 4 * '../')
RISCV_DV_ROOT = os.path.normpath(os.path.join(IBEX_ROOT,
                                              'vendor/google_riscv-dv'))


def run_one(verbose: bool,
            cmd: List[str],
            discard_stdstreams: bool = False) -> int:
    '''Run a command, returning its return code

    If verbose is true, print the command to stderr first (a bit like bash -x).

    If discard_stdstreams is true, redirect stdout and stderr in the subprocess
    to /dev/null. This seems a bit crazy, but makes sense for EDA tools that
    have a '-l' argument that takes a path to which they write a copy of
    everything that was going out on stdout/stderr.

    '''
    stdstream_dest = None
    shell_redirection = ''
    if discard_stdstreams:
        stdstream_dest = subprocess.DEVNULL
        shell_redirection = ' >/dev/null 2>&1'

    if verbose:
        # The equivalent of bash -x
        cmd_str = ' '.join(shlex.quote(w) for w in cmd) + shell_redirection
        print('+ ' + cmd_str, file=sys.stderr)

    # Passing close_fds=False ensures that if cmd is a call to Make then we'll
    # pass through the jobserver fds. If you don't do this, you get a warning
    # starting "warning: jobserver unavailable".
    return subprocess.run(cmd,
                          stdout=stdstream_dest,
                          stderr=stdstream_dest,
                          close_fds=False).returncode


def start_riscv_dv_run_cmd(verbose: bool):
    '''Return the command parts of a call to riscv-dv's run.py'''
    riscv_dv_extension = os.path.join(THIS_DIR, '../riscv_dv_extension')

    csr_desc = os.path.join(riscv_dv_extension, 'csr_description.yaml')
    testlist = os.path.join(riscv_dv_extension, 'testlist.yaml')

    cmd = ['python3',
           os.path.join(RISCV_DV_ROOT, 'run.py'),
           '--testlist', testlist,
           '--gcc_opts=-mno-strict-align',
           '--custom_target', riscv_dv_extension,
           '--csr_yaml', csr_desc,
           '--mabi=ilp32']
    if verbose:
        cmd.append('--verbose')

    return cmd
