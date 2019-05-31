# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Setting IP_NAME and PRJ_DIR. Assuming Makefile located at `hw/ip/<ip_name>/dv`
DV_DIR    := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
IP_DIR    := $(subst /dv,,${DV_DIR})
wordslist := $(subst /, ,${IP_DIR})
IP_NAME   := $(lastword ${wordslist})
GEN_DIR   := $(realpath ${DV_DIR}/../vendor/google_riscv-dv)
TOOLCHAIN := ${RISCV_TOOLCHAIN}
OUT       := "${DV_DIR}/out"
# Run time options for the instruction generator
GEN_OPTS  :=
# Run time options for ibex RTL simulation
SIM_OPTS  :=
# Enable waveform dumping
WAVES     := 1
WAVE_CMP_OPTS := -debug_access+all -ucli -do vcs.tcl
# Enable coverage dump
COV       := 0

ifeq (${WAVES}, 0)
	WAVE_CMP_OPTS=
endif

SHELL=/bin/bash

export PRJ_DIR:= $(realpath ${DV_DIR}/../..)

tests = core_ibex_base_test
test_bin = ${DV_DIR}/tests/bin/ibex_sanity_test.bin

rand:=$(shell awk 'BEGIN{srand();printf("%d", 65536*rand())}')

.PHONY: rtl_sim clean iss_sim

all: clean gen iss_sim compile rtl_sim post_compare

clean:
	rm -rf ${OUT}

# Generate random instructions
gen:
	mkdir -p ${OUT}
	cd ${GEN_DIR}; ./run -o ${OUT}/instr_gen ${GEN_OPTS};

# ISS simulation
iss_sim:
	cd ${GEN_DIR}; \
	./iss_sim -dir ${OUT}/instr_gen -toolchain ${TOOLCHAIN} -isa rv32imc -abi ilp32;

# Compile ibex core TB
compile:
	mkdir -p ${OUT}/rtl_sim
	vcs -f ${IP_NAME}_dv.f  -full64 \
      -l ${OUT}/rtl_sim/compile.log  \
      -sverilog -ntb_opts uvm-1.2 \
      +define+UVM_REGEX_NO_DPI -timescale=1ns/10ps -licqueue \
      -Mdir=${OUT}/rtl_sim/vcs_simv.csrc \
      -o ${OUT}/rtl_sim/vcs_simv \
      +define+BOOT_ADDR=32\'h8000_0000 \
      +define+TRACE_EXECUTION \
      -debug_access+pp \
      ${WAVE_CMP_OPTS} \
      -lca -kdb

# Run ibex RTL simulation with random instructions
rtl_sim:
	./sim ${SIM_OPTS} -dir ${OUT} -waves ${WAVES}

# Compare the regression result between ISS and RTL sim
post_compare:
	./compare ${OUT}
