#!/usr/bin/env python3
"""Compile the different test sources to create binaries, ready for simulation."""

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


import argparse
from typing import Tuple, Dict, List
import os
import shlex
import sys
import tempfile
import pathlib3x as pathlib

from scripts_lib import run_one, format_to_cmd, read_yaml
import riscvdv_interface
from test_entry import read_test_dot_seed
from metadata import RegressionMetadata
from test_run_result import TestRunResult, TestType

import logging
logger = logging.getLogger(__name__)


def get_riscvdv_compile_cmds(md: RegressionMetadata, trr: TestRunResult) -> List[str]:
    """Run riscv-dv to get a list of build/compilation commands.

    These will need some massaging to match our paths, but we can't generate the
    commands by hand because there are several test-specific options that might appear.
    """
    with tempfile.TemporaryDirectory() as td_fd:
        td = pathlib.Path(td_fd)
        placeholder = td/'@@PLACEHOLDER@@'
        orig_list = td/'orig-cmds.list'

        cmd = (riscvdv_interface.get_run_cmd(bool(md.verbose)) +
               ['--verbose',
                '--output', placeholder,
                '--steps=gcc_compile',
                '--test', trr.testname,
                '--start_seed', str(trr.seed),
                '--iterations', '1',
                '--isa', md.isa_ibex,
                '--debug', orig_list])  # Use the --debug output to capture the original commands

        trr.compile_asm_gen_log = trr.dir_test / 'compile_gen.riscv-dv.log'
        trr.compile_asm_gen_cmds = [format_to_cmd(cmd)]

        dv_ret = run_one(verbose=md.verbose,
                         cmd=trr.compile_asm_gen_cmds[0],
                         redirect_stdstreams=trr.compile_asm_gen_log)
        if dv_ret:
            return dv_ret

        orig_cmds = []
        with open(orig_list) as fd:
            for line in fd:
                line = line.strip()
                if line:
                    orig_cmds.append(shlex.split(line))

    # Do the massaging. We intentionally used "@@PLACEHOLDER@@" as a path in
    # our call to riscv-dv, which should let us find all the things that matter
    # easily.
    trr.objectfile = trr.dir_test/'test.o'
    trr.binary = trr.dir_test/'test.bin'

    rewrites = [
        (f"{placeholder}/asm_test/{trr.testname}_0.S", str(trr.assembly)),
        (f"{placeholder}/asm_test/{trr.testname}_0.o", str(trr.objectfile)),
        (f"{placeholder}/asm_test/{trr.testname}_0.bin", str(trr.binary))
    ]

    new_cmds = []
    for cmd in orig_cmds:
        new_cmd = []
        for word in cmd:
            for old, new in rewrites:
                word = word.replace(old, new)

            if str(placeholder) in word:
                raise RuntimeError("Couldn't replace every copy of "
                                   f"placeholder in {cmd}")

            new_cmd.append(word)
        new_cmds.append(new_cmd)

    return new_cmds


def get_directed_compile_cmds(md: RegressionMetadata, trr: TestRunResult) -> List[str]:
    """Construct the build/compilation commands from the directed_testlist data."""

    env = os.environ.copy()
    for e in ['RISCV_TOOLCHAIN', 'RISCV_GCC', 'RISCV_OBJCOPY']:
        if e not in env:
            raise RuntimeError("Missing required environment variables for the RISCV TOOLCHAIN")

    # Get the data from the directed test yaml that we need to construct the command.
    directed_data = read_yaml(md.directed_test_data)
    trr.directed_data = next(filter(lambda item: (item.get('test') == trr.testname), directed_data), None)

    directed_dir = md.directed_test_dir
    includes = directed_dir/(pathlib.Path(trr.directed_data.get('includes')))
    ld = directed_dir/(pathlib.Path(trr.directed_data.get('ld_script')))

    trr.assembly = directed_dir/trr.directed_data.get('test_srcs')
    trr.objectfile = trr.dir_test/'test.o'
    trr.binary = trr.dir_test/'test.bin'

    # Compose the compilation command
    riscv_gcc_arg = trr.directed_data.get('gcc_opts') + \
                    f" -I{includes}" + \
                    f" -T{ld}"
    riscv_gcc_cmd = " ".join([env.get('RISCV_GCC'),
                              riscv_gcc_arg,
                              f"-o {trr.objectfile}",
                              f"{trr.assembly}"])
    riscv_gcc_bin_cmd = " ".join([env.get('RISCV_OBJCOPY'),
                              f"-O binary {trr.objectfile}",
                              f"{trr.binary}"])
    return [shlex.split(riscv_gcc_cmd), shlex.split(riscv_gcc_bin_cmd)]


def _main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    parser.add_argument('--test-dot-seed', type=read_test_dot_seed, required=False)
    parser.add_argument('--bin', type=pathlib.Path, required=False)
    args = parser.parse_args()
    tds = args.test_dot_seed
    md = RegressionMetadata.construct_from_metadata_dir(args.dir_metadata)
    trr = TestRunResult.construct_from_metadata_dir(args.dir_metadata, f"{tds[0]}.{tds[1]}")

    if trr.testtype == TestType.RISCVDV:
        cmds = get_riscvdv_compile_cmds(md, trr)
        trr.compile_asm_log = trr.dir_test/'compile.riscvdv.log'
    if trr.testtype == TestType.DIRECTED:
        cmds = get_directed_compile_cmds(md, trr)
        trr.compile_asm_log = trr.dir_test/'compile.directed.log'

    # Finally, run all the commands
    trr.compile_asm_cmds = [format_to_cmd(cmd) for cmd in cmds]
    trr.export(write_yaml=True)

    for cmd in trr.compile_asm_cmds:
        ret = run_one(md.verbose, cmd)
        if ret != 0:
            return ret


if __name__ == '__main__':
    sys.exit(_main())
