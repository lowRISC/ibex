#!/usr/bin/env bash

# Prototype TestRIG Xcelium BUILD script
#
# TODO: Replace this script with Makefile rules
#
# Usage:
#   Call this script from the directory it is stored in.
#   Add '-c' for coverage collection.


export PRJ_DIR=$(realpath ../../../)
export LOWRISC_IP_DIR=$(realpath ${PRJ_DIR}/vendor/lowrisc_ip/)

# Needed for tcl files that are used with Cadence tools.
export dv_root=$(realpath ${LOWRISC_IP_DIR}/dv)
export DUT_TOP="ibex_top"

mkdir -p xlm_testrig_out

coverage_arg=""

while getopts "c" opt; do
  case $opt in
      c) coverage_arg="\
  -coverage all \
  -nowarn COVDEF \
  -covfile "${LOWRISC_IP_DIR}/dv/tools/xcelium/testrig-cover.ccf" \
  -covdut ibex_top" ;;
   esac
done

xrun \
  -64bit \
  -f ibex_testrig_dv.f \
  -l xlm_testrig_out/build.log \
  -xmlibdirname xlm_testrig_out/xcelium.d \
  -sv \
  -uvmhome CDNS-1.2 \
  +define+XCELIUM \
  -licqueue \
  -timescale 1ns/10ps \
  -elaborate \
  -access rwc \
  -I"${PRJ_DIR}/vendor/socket_packet_utils" \
  $coverage_arg
