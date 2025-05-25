#!/usr/bin/env python3
"""Helper-scripts to merge coverage databases across multiple tests."""

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


import argparse
import os
import sys
import pathlib3x as pathlib
from typing import Set

from metadata import RegressionMetadata, LockedMetadata
from setup_imports import _OT_LOWRISC_IP
from scripts_lib import run_one

import logging
logger = logging.getLogger(__name__)

def find_cov_dbs(start_dir: pathlib.Path, simulator: str) -> Set[pathlib.Path]:
    """Gather the paths of all individual coverage databases for each test.

    Each EDA tool may have a different format in which they save this data from the
    run-phase, so use rglobs to locate these files relative to start_dir.
    """
    cov_dbs = set()

    if simulator == 'xlm':
        for p in start_dir.glob('**/*.ucd'):
            logger.info(f"Found coverage database (ucd) at {p}")
            cov_dbs.add(p)
    if simulator == 'vcs':
        for p in start_dir.glob('**/test.vdb'):
            logger.info(f"Found coverage database (vdb) at {p}")
            cov_dbs.add(p)

    if not cov_dbs:
        logger.info(f"No coverage found for {simulator}")
        return ()

    return cov_dbs


def merge_cov_vcs(md: RegressionMetadata, cov_dirs: Set[pathlib.Path]) -> int:
    """Invoke 'urg' to merge the vcs coverage databases for each individual test

    Returns: the retcode of the urg merge command.
    """
    cmd = (
        ['urg',
         '-full64',
         '-format', 'both',
         '-dbname', str(md.dir_cov/'merged.vdb'),
         '-report', str(md.dir_cov/'report'),
         '-log', str(md.dir_cov/'merge.log'),
         '-dir'] + [str(cov_dir) for cov_dir in list(cov_dirs)]
    )

    with LockedMetadata(md.dir_metadata, __file__) as md:
        md.cov_merge_log = md.dir_cov / 'merge.log'
        md.cov_merge_stdout = md.dir_cov / 'merge.log.stdout'
        md.cov_merge_cmds = [cmd]

    with open(md.cov_merge_stdout, 'wb') as fd:
        logger.info("Generating merged coverage directory")
        merge_ret = run_one(md.verbose, cmd, redirect_stdstreams=fd)

    if merge_ret:
        logger.warning(f"WARNING: Saw non-zero retcode while merging coverage : logfile -> {trr.cov_merge_stdout}")
    return merge_ret

def merge_cov_xlm(md: RegressionMetadata, cov_dbs: Set[pathlib.Path]) -> int:
    """Merge xcelium-generated coverage using the OT scripts.

    The vendored-in OpenTitan IP contains .tcl scripts that can merge xcelium
    coverage using the Cadence 'imc' Integrated-Metrics-Centre tool.

    Returns: the retcode of the imc merge command.
    """
    xcelium_scripts = _OT_LOWRISC_IP/'dv/tools/xcelium'

    imc_cmd = ["imc", "-64bit", "-licqueue"]

    # Update the metdadata file with the commands we're about to run
    with LockedMetadata(md.dir_metadata, __file__) as md:

        md.cov_merge_db_list = md.dir_cov / 'cov_db_runfile'
        md.cov_merge_log = md.dir_cov / 'merge.log'
        md.cov_merge_stdout = md.dir_cov / 'merge.log.stdout'
        md.cov_merge_cmds = [(imc_cmd + ["-exec", str(xcelium_scripts / "cov_merge.tcl"),
                                         "-logfile", str(md.dir_cov / 'merge.log')])]

        md.cov_report_log = md.dir_cov / 'report.log'
        md.cov_report_stdout = md.dir_cov / 'report.log.stdout'
        md.cov_report_cmds = [(imc_cmd + ["-load", str(md.dir_cov_merged),
                                          "-init", str(md.ibex_dv_root / "waivers" / "coverage_waivers_xlm.tcl"),
                                          "-exec", str(xcelium_scripts / "cov_report.tcl"),
                                          "-logfile", str(md.dir_cov / 'report.log')])]

    # Dump the list of databases to a runfile, which will be read by the .tcl script
    # This prevents the argument list from getting too long for an environment variable when using lots of iterations
    # > The paths in the <runfile> should be listed one per line.
    # > The path to the <runfile> should be set in the environment variable 'cov_db_runfile'
    md.cov_merge_db_list.write_text( ('\n'.join(str(d.parent) for d in cov_dbs)) + '\n')

    # Setup any environment variables needed by the coverage merge TCL scripts
    # - cov_merge_db_dir : The location to output the merged coverage database
    # - cov_report_dir : The location to output the reports database
    # - cov_db_dirs : (Unused) A list of individual coverage databases to be merged
    # - cov_db_runfile : The location of a file containing all individual coverage databases to be merged
    # - DUT_TOP : Top-level module name of the DUT
    xlm_cov_dirs = {
        'cov_merge_db_dir': str(md.dir_cov_merged),
        'cov_report_dir': str(md.dir_cov_report),
        'cov_db_dirs': "",
        'cov_db_runfile': str(md.cov_merge_db_list),
        "DUT_TOP": md.dut_cov_rtl_path
    }
    logger.info(f"xlm_cov_dirs : {xlm_cov_dirs}")

    xlm_env = os.environ.copy()
    xlm_env.update(xlm_cov_dirs)

    # First do the merge
    md.dir_cov_merged.mkdir(exist_ok=True, parents=True)
    with open(md.cov_merge_stdout, 'wb') as fd:
        merge_ret = run_one(verbose=md.verbose,
                            cmd=md.cov_merge_cmds[0],
                            redirect_stdstreams=fd,
                            env=xlm_env)
    if merge_ret:
        logger.warning(f"WARNING: Saw non-zero retcode while merging coverage : logfile -> {md.cov_merge_stdout}")
        return merge_ret

    # Then do the reporting
    os.makedirs(md.dir_cov_report, exist_ok=True)
    with open(md.cov_report_stdout, 'wb') as fd:
        report_ret = run_one(verbose=md.verbose,
                             cmd=md.cov_report_cmds[0],
                             redirect_stdstreams=fd,
                             env=xlm_env)

    if report_ret:
        logger.warning(f"WARNING: Saw non-zero retcode while reporting coverage : logfile -> {trr.cov_report_stdout}")
    return report_ret


def main():
    '''Entry point when run as a script'''
    parser = argparse.ArgumentParser()
    parser.add_argument('--dir-metadata', type=pathlib.Path, required=True)
    args = parser.parse_args()
    md = RegressionMetadata.construct_from_metadata_dir(args.dir_metadata)

    if md.simulator not in ['xlm', 'vcs']:
        raise ValueError(f'Unsupported simulator for merging coverage: {args.simulator}')

    if md.verbose:
        logging.basicConfig()
        logging.getLogger().setLevel(logging.DEBUG)  # root -> most-permissive
        logger.setLevel(logging.INFO)

    md.dir_cov.mkdir(exist_ok=True, parents=True)

    # Compile a list of all the coverage databases
    cov_dbs = find_cov_dbs(md.dir_run, md.simulator)
    if not cov_dbs:
        logger.error("No coverage databases found. Unable to continue.")
        return 1

    # Call the appropriate merge function for each tool, returning the retcode of
    # the subprocess tasks.
    merge_funs = {
        'vcs': merge_cov_vcs,
        'xlm': merge_cov_xlm
    }
    return merge_funs[md.simulator](md, cov_dbs)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except RuntimeError as err:
        sys.stderr.write('Error: {}\n'.format(err))
        sys.exit(1)
