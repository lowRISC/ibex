#!/usr/bin/env bash

if [ "$#" -ne "1" ]; then
  echo 'Provide exactly one argument, namely a directory containing a coverage database'
  exit 1
fi
cov_db_dir="$1"
if [ ! -d "$cov_db_dir" ]; then
  echo 'Specified directory does not exist'
  exit 1
fi

export PRJ_DIR=$(realpath ../../../)
export LOWRISC_IP_DIR=$(realpath ${PRJ_DIR}/vendor/lowrisc_ip/)

# Needed for cov_report.tcl
export dv_root=$(realpath ${LOWRISC_IP_DIR}/dv)
export DUT_TOP="ibex_top"
export cov_report_dir="xlm_testrig_out/report"
export cov_merge_db_dir="$cov_db_dir"

mkdir -p "$cov_report_dir"

# Generate coverage reports
imc \
  -64bit \
  -logfile xlm_testrig_out/report.log \
  -licqueue \
  -init waivers/coverage_waivers_xlm.tcl \
  -load "$cov_db_dir" \
  -exec "${dv_root}/tools/xcelium/cov_report.tcl"
