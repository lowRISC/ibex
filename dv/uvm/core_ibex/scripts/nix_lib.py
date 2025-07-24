#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import os
import subprocess
import pathlib3x as pathlib


import logging
logger = logging.getLogger(__name__)
logger.setLevel(logging.INFO)


def patch_rpath(so: pathlib.Path):
    """Patch the rpath of the simulation executable to resolve stdenv.cc correctly."""
    nix_gcc_lib_path = os.getenv("IBEX_NIX_SHELL_LIB")

    # Get the old rpath
    cmd = ["patchelf", "--print-rpath", str(so)]
    old_rpath = subprocess.check_output(cmd).decode()
    logger.warning(f"Old rpath : {old_rpath}")

    # Add the nix gcc lib path to the head of the shared library's RPATH
    new_rpath_str = f"{nix_gcc_lib_path}:{old_rpath}"
    cmd = ["patchelf", "--set-rpath", new_rpath_str, str(so)]
    new_rpath_output = subprocess.check_output(cmd).decode()
    logger.warning(f"Output of --set-rpath : {new_rpath_output}")

    # Print the new rpath
    cmd = ["patchelf", "--print-rpath", str(so)]
    new_rpath = subprocess.check_output(cmd).decode()
    logger.warning(f"New rpath : {new_rpath}")

def patch_dtneeded(so: pathlib.Path):
    """Patch some stdenv.cc shared library deps of the simulation .so to be static."""
    # We need to setup a couple of .so deps to be static, as the 'xrun' utility
    # uses it's own search paths when discovering shared-library deps for the librun.so
    # when simulating.
    nix_gcc_lib_path = os.getenv("IBEX_NIX_SHELL_LIB")

    cmd1 = ["patchelf", "--replace-needed", "libstdc++.so.6", f"{nix_gcc_lib_path}/libstdc++.so.6", str(so)]
    cmd2 = ["patchelf", "--replace-needed", "libgcc_s.so.1", f"{nix_gcc_lib_path}/libgcc_s.so.1", str(so)]

    subprocess.check_output(cmd1)
    subprocess.check_output(cmd2)

