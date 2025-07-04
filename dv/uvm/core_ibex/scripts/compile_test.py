#!/usr/bin/env python3

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Compile the different test sources to create binaries, ready for simulation."""

import argparse
from typing import Tuple, Dict, List
import os
import shlex
import sys
import tempfile
import pathlib3x as pathlib
import itertools

from scripts_lib import run_one, format_to_cmd, read_yaml
import riscvdv_interface
from test_entry import read_test_dot_seed, get_test_entry
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


    if (trr.testtype == TestType.RISCVDV and trr.is_discrete_debug_module):
        logger.warning(f"Using discrete debug module memory layout.")

        # Remove the objdump command for the single contiguous memory region.
        # (If debug module address is far from the boot_address, a single loadable
        # .bin file can be very large (roughly 1.6Gb for the default address params))
        new_cmds.pop()

        # Replace default riscv-dv linker script with custom script
        for cmd in new_cmds:
            for index, token in enumerate(cmd):
                if token.startswith("-T"):
                    cmd[index] = "-T" + str(md.ibex_riscvdv_customtarget / 'ddm_link.ld')

        # Generate binary outputs for the different LOADABLE memory regions (main, dm).
        # The linker script places some sections inside the 'dm' memory region,
        # which may be quite far away from the 'main' memory. To avoid
        # generating a very large uncompressed binary file to LOAD both
        # segments, we probably want to use the .vmem format passed to
        # $readmemh to initialize the RTL-side memory model. However, as the
        # cosim memory model is initialized over the DPI interface, and may be
        # comprised of multiple 'memories' rather than a single contiguous
        # space, we can't simply rely on $readmemh to automatically partition a
        # single file across multiple arrays. Hence for it's initialization,
        # generate raw .bin files which will be loaded via the base address of
        # each section.

        # The following sections are within the loadable 'dm' region
        dm_sections = [".debug_module", ".dm_scratch"]

        # The following objcopy arguments generate outputs with only a subset of the sections
        # present in the object file.
        flatten_list = lambda unflat_list: list(itertools.chain(*unflat_list))
        only_sections = flatten_list([["--only-section", s] for s in dm_sections])
        remove_sections = flatten_list([["--remove-section", s] for s in dm_sections])

        env = os.environ.copy()
        objcopy = env.get('RISCV_OBJCOPY')

        # Generate verilog memory formatted outputs (.vmem)

        trr.vmem_main = trr.dir_test / "test.main.vmem"
        trr.vmem_dm = trr.dir_test / "test.dm.vmem"
        vmem_dm_cmd = \
            [objcopy, "-O", "verilog", *only_sections, f"{trr.objectfile}", f"{trr.vmem_dm}"]
        vmem_main_cmd = \
            [objcopy, "-O", "verilog", *remove_sections, f"{trr.objectfile}", f"{trr.vmem_main}"]

        # Generate binary-formatted outputs (.bin)

        trr.binary_main = trr.dir_test / "test.main.bin"
        trr.binary_dm = trr.dir_test / "test.dm.bin"
        bin_dm_cmd = \
            [objcopy, "-O", "binary", *only_sections, f"{trr.objectfile}", f"{trr.binary_dm}"]
        bin_main_cmd = \
            [objcopy, "-O", "binary", *remove_sections, f"{trr.objectfile}", f"{trr.binary_main}"]

        new_cmds.extend([vmem_dm_cmd, vmem_main_cmd, bin_dm_cmd, bin_main_cmd])

    return new_cmds


def get_directed_compile_cmds(md: RegressionMetadata, trr: TestRunResult) -> List[str]:
    """Construct the build/compilation commands from the directed_testlist data."""

    env = os.environ.copy()
    for e in ['RISCV_TOOLCHAIN', 'RISCV_GCC', 'RISCV_OBJCOPY']:
        if e not in env:
            raise RuntimeError("Missing required environment variables for the RISCV TOOLCHAIN")

    trr.assembly = trr.directed_data.get('test_srcs')
    trr.objectfile = trr.dir_test/'test.o'
    trr.binary = trr.dir_test/'test.bin'

    # Compose the compilation commands
    riscv_gcc_cmd = " ".join([env.get('RISCV_GCC'),
                              trr.directed_data.get('gcc_opts'),
                              f"-I{trr.directed_data.get('includes')}",
                              f"-T{trr.directed_data.get('ld_script')}",
                              f"-o {trr.objectfile}",
                              f"{trr.assembly}"])
    riscv_gcc_bin_cmd = " ".join([env.get('RISCV_OBJCOPY'),
                                  f"-O binary {trr.objectfile}",
                                  f"{trr.binary}"])
    return [shlex.split(riscv_gcc_cmd), shlex.split(riscv_gcc_bin_cmd)]


def _main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    parser.add_argument('--test-dot-seed', type=read_test_dot_seed, required=True)
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

    trr.compile_asm_cmds = [format_to_cmd(cmd) for cmd in cmds]
    trr.export(write_yaml=True)

    # Finally, run all the commands
    with trr.compile_asm_log.open('wb') as fd:
        for cmd in trr.compile_asm_cmds:
            ret = run_one(md.verbose, cmd, redirect_stdstreams=fd)
            if ret != 0:
                return ret


if __name__ == '__main__':
    sys.exit(_main())
