#!/bin/bash
# Dockerfile entrypoint for ibex verification according to azure-pipelines.yml

# In this script there are all steps depending on tested code.
# All static dependencies are in Dockerfile.
# The directory with ibex repository should be mounted in /home/ibex/repo

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Initial styling variables
bold=$(tput bold)
normal=$(tput sgr0)
red='\033[0;31m'
nc='\033[0m' # No Color


## Display environment
printf "\n${bold}Step: Display environment${normal}\n\n"

echo $PATH
python3 --version
echo -n "fusesoc "
fusesoc --version
verilator --version
riscv32-unknown-elf-gcc --version


## Lint Verilog source files with Verilator
printf "\n${bold}Step: Lint Verilog source files with Verilator${normal}\n\n"

fusesoc --cores-root . run --target=lint lowrisc:ibex:ibex_core_tracing
if [ $? != 0 ]; then
  echo "${red}Verilog lint failed. Run 'fusesoc --cores-root . run --target=lint lowrisc:ibex:ibex_core_tracing' to check and fix all errors.${nc}"
  exit 1
fi


## Run RISC-V Compliance test for Ibex RV32IMC
printf "\n${bold}Step: Run RISC-V Compliance test for Ibex RV32IMC${normal}\n\n"

# Build simulation model of Ibex
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ibex:ibex_riscv_compliance --RV32M=1 --RV32E=0
if [ $? != 0 ]; then
  echo "${red}Unable to build Verilator model of Ibex for compliance testing.${nc}"
  exit 1
fi

# Run compliance test suite
export TARGET_SIM=$PWD/build/lowrisc_ibex_ibex_riscv_compliance_0.1/sim-verilator/Vibex_riscv_compliance
export RISCV_PREFIX=riscv32-unknown-elf-
export RISCV_TARGET=ibex
export RISCV_DEVICE=rv32imc
fail=0
for isa in rv32i rv32im rv32imc; do
  make -C /home/ibex/build/riscv-compliance RISCV_ISA=$isa 2>&1 | tee run.log
  if [ ${PIPESTATUS[0]} != 0 ]; then
    echo "${red}The RISC-V compliance test suite failed for $isa"

    # There's no easy way to get the test results in machine-readable
    # form to properly exclude known-failing tests. Going with an
    # approximate solution for now.
    if [ $isa == rv32i ] && grep -q 'FAIL: 5/55' run.log; then
      echo "${red}Expected failure for rv32i, see lowrisc/ibex#100 more more information.${nc}"
    else
      fail=1
    fi
  fi
done
exit $fail
