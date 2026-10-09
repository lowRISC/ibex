#!/usr/bin/env bash

# Prototype TestRIG Xcelium RUN script
#
# TODO: Replace this script with Makefile rules
#
# Usage:
#   Call this script from the directory it is stored in,
#   and in another terminal run TestRIG with a manual implementation.
#   Add '-c' for coverage collection,
#       '-w' for waveform capture,
#       '-v' for high UVM verbosity.

datetime=$(date +%F_%H%M.%S)

coverage_arg=""
verbosity_arg="+UVM_VERBOSITY=UVM_LOW"
wave_arg=""

while getopts "cvw" opt; do
  case $opt in
      c) coverage_arg="\
  -covmodeldir xlm_testrig_out/coverage \
  -covworkdir xlm_testrig_out \
  -covscope coverage \
  -covtest ${datetime} \
  +enable_ibex_fcov=1" ;;
      v) verbosity_arg="+UVM_VERBOSITY=UVM_HIGH" ;;
      w) wave_arg="-input waves.tcl" ;;
   esac
done

# Run Xcelium (which will wait for a connection from TestRIG)
xrun \
  -64bit \
  -R \
  -l xlm_testrig_out/run.log \
  -xmlibdirname xlm_testrig_out/xcelium.d \
  +UVM_TESTNAME=core_ibex_testrig_test \
  -licqueue \
  $coverage_arg \
  $wave_arg \
  $verbosity_arg
