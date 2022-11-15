#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Run an elf against simple system co-simulation and check the UART output for
# reported pass/fail reporting as appropriate for use in Azure pipelines

SKIP_PASS_CHECK=0

if [ $# -eq 3 ]; then
  if [ $1 == "--skip-pass-check" ]; then
    SKIP_PASS_CHECK=1
  fi

  TEST_NAME=$2
  TEST_ELF=$3
elif [ $# -eq 2 ]; then
  TEST_NAME=$1
  TEST_ELF=$2
else
 echo "Usage: $0 [--skip-pass-check] test_name test_elf"
 exit 1
fi

echo "Running $TEST_NAME with co-simulation"
build/lowrisc_ibex_ibex_simple_system_cosim_0/sim-verilator/Vibex_simple_system --meminit=ram,$TEST_ELF
if [ $? != 0 ]; then
  echo "##vso[task.logissue type=error]Running % failed co-simulation testing"
  exit 1
fi

grep 'FAILURE' ibex_simple_system.log
if [ $? != 1 ]; then
  echo "##vso[task.logissue type=error]Failure seen in $TEST_NAME log"
  echo "Log contents:"
  cat ibex_simple_system.log
  exit 1
fi

if [ $SKIP_PASS_CHECK != 1 ]; then
  grep 'PASS' ibex_simple_system.log
  if [ $? != 0 ]; then
    echo "##vso[task.logissue type=error]No pass seen in $TEST_NAME log"
    echo "Log contents:"
    cat ibex_simple_system.log
    exit 1
  fi
fi

echo "$TEST_NAME succeeded"
