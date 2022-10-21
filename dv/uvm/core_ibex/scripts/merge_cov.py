#!/usr/bin/env python3
"""Helper-scripts to merge coverage databases across multiple tests."""

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


import argparse
import logging
import os
import shutil
import sys
import pathlib3x as pathlib
from typing import Set

from metadata import RegressionMetadata, LockedMetadata
from setup_imports import _OT_LOWRISC_IP
from scripts_lib import run_one


def find_cov_dirs(start_dir: pathlib.Path, simulator: str) -> Set[pathlib.Path]:
    """Gather a set of the coverage databases/directories."""
    cov_dirs = set()

    if simulator == 'xlm':
        for p in start_dir.glob('**/*.ucd'):
            logging.info(f"Found coverage database (ucd) at {p}")
            cov_dirs.add(p.parent)
    if simulator == 'vcs':
        for p in start_dir.glob('**/test.vdb'):
            logging.info(f"Found coverage database (vdb) at {p}")
            cov_dirs.add(p.parent)

    if not cov_dirs:
        logging.info(f"No coverage found for {simulator}")
        return 1

    return cov_dirs


def merge_cov_vcs(md: RegressionMetadata, cov_dirs: Set[pathlib.Path]) -> int:
    logging.info("Generating merged coverage directory")
    cmd = (['urg', '-full64',
            '-format', 'both',
            '-dbname', str(md.cov_dir/'merged.vdb'),
            '-report', str(md.cov_dir/'report'),
            '-log', str(md.cov_dir/'merge.log'),
            '-dir'] +
           list(cov_dirs))
    return run_one(md.verbose, cmd, redirect_stdstreams='/dev/null')


def merge_cov_xlm(md: RegressionMetadata, cov_dirs: Set[pathlib.Path]) -> int:
    """Merge xcelium-generated coverage using the OT scripts.

    The vendored-in OpenTitan IP contains .tcl scripts that can merge xcelium
    coverage using the Cadnece 'imc' Integrated-Metrics-Centre tool.

    """
    xcelium_scripts = _OT_LOWRISC_IP/'dv/tools/xcelium'

    # The merge TCL code uses a glob to find all available scopes and previous
    # runs. In order to actually get the databases we need to go up once so
    # that the "*" finds the directory we've seen.
    cov_dir_parents = ' '.join(str(d.parent) for d in cov_dirs)

    # Get all needed directories for merge and report stages.
    xlm_cov_dirs = {
        'cov_merge_db_dir': str(md.dir_cov_merged),
        'cov_report_dir': str(md.dir_cov_report),
        'cov_db_dirs': cov_dir_parents
    }
    logging.info(f"xlm_cov_dirs : {xlm_cov_dirs}")

    # Finally, set an environment variable containing all the directories that
    # should be merged (this is how the list gets passed down to the TCL script
    # that handles them)

    xlm_env = os.environ.copy()
    xlm_env.update(xlm_cov_dirs)

    imc_cmd = ["imc", "-64bit", "-licqueue"]

    # Update the metdadata file with the commands we're about to run
    with LockedMetadata(md.dir_metadata, __file__) as md:

        md.cov_merge_log = md.dir_cov / 'merge.log'
        md.cov_merge_stdout = md.dir_cov / 'merge.log.stdout'
        md.cov_merge_cmds = [(imc_cmd + ["-exec", str(xcelium_scripts/"cov_merge.tcl"),
                                         "-logfile", str(md.dir_cov/'merge.log')])]

        md.cov_report_log = md.dir_cov / 'report.log'
        md.cov_report_stdout = md.dir_cov / 'report.log.stdout'
        md.cov_report_cmds = [(imc_cmd + ["-load", str(md.dir_cov_merged),
                                          "-exec", str(xcelium_scripts/"cov_report.tcl"),
                                          "-logfile", str(md.dir_cov/'report.log')])]

    # First do the merge
    md.dir_cov_merged.mkdir(exist_ok=True, parents=True)
    with open(md.cov_merge_stdout, 'wb') as fd:
        merge_ret = run_one(verbose=md.verbose,
                            cmd=md.cov_merge_cmds[0],
                            redirect_stdstreams=fd,
                            env=xlm_env)
    if merge_ret:
        return merge_ret

    # Then do the reporting
    os.makedirs(md.dir_cov_report, exist_ok=True)
    with open(md.cov_report_stdout, 'wb') as fd:
        report_ret = run_one(verbose=md.verbose,
                             cmd=md.cov_report_cmds[0],
                             redirect_stdstreams=fd,
                             env=xlm_env)

    return report_ret


def main():
    '''Entry point when run as a script'''
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    args = parser.parse_args()
    md = RegressionMetadata.construct_from_metadata_dir(args.dir_metadata)

    if md.simulator not in ['xlm', 'vcs']:
        raise ValueError(f'Unsupported simulator for merging coverage: {args.simulator}')

    md.dir_cov.mkdir(exist_ok=True, parents=True)

    # Compile a list of all directories that contain coverage databases
    cov_dirs = find_cov_dirs(md.dir_run, md.simulator)

    merge_funs = {
        'vcs': merge_cov_vcs,
        'xlm': merge_cov_xlm
    }
    return merge_funs[md.simulator](md, cov_dirs)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except RuntimeError as err:
        sys.stderr.write('Error: {}\n'.format(err))
        sys.exit(1)
