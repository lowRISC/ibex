# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Top-Level Makefile
###############################################################################

.SUFFIXES:
export

# Explicitly ask for the bash shell
SHELL := bash

# Build the 'all' target by default, override with e.g. GOAL=rtl_tb_compile
GOAL ?= all

###############################################################################
# CONFIGURATION KNOBS

# Seed for instruction generator and RTL simulation
#
# By default, SEED is set to a different value on each run by picking a random
# value in the Makefile. For overnight testing, a sensible seed might be
# something like the output of "date +%y%m%d". For regression testing, you'll
# need to make sure that a the seed for a failed test "sticks" (so we don't
# start passing again without fixing the bug).
SEED                := $(shell echo $$RANDOM)

# Enable waveform dumping
WAVES               := 0
# Enable coverage dump
COV                 := 0
# RTL simulator (xlm, vcs, questa, dsim, )
SIMULATOR           := xlm
# ISS (spike, ovpsim)
ISS                 := spike
# Test name (default: full regression)
TEST                := all
RISCV-DV-TESTLIST   := riscv_dv_extension/testlist.yaml
DIRECTED-TESTLIST   := directed_tests/directed_testlist.yaml
# Verbose logging
VERBOSE             := 0
# Number of iterations for each test, assign a non-empty value to override the
# iteration count in the test list
ITERATIONS          :=
# Pass/fail signature address at the end of test (see riscv_dv handshake documentation)
SIGNATURE_ADDR      := 8ffffffc

### Ibex top level parameters ###
IBEX_CONFIG         := opentitan

# Path to DUT used for coverage reports
DUT_COV_RTL_PATH    := "ibex_top"

# Optional override for compressed extension subset.
# Empty means: use RV32ZC from IBEX_CONFIG in ibex_configs.yaml.
# Allowed values:
#   ibex_pkg::RV32Zca
#   ibex_pkg::RV32ZcaZcb
#   ibex_pkg::RV32ZcaZcmp
#   ibex_pkg::RV32ZcaZcbZcmp
RV32ZC :=

export EXTRA_COSIM_CFLAGS ?=

ifeq ($(COSIM_SIGSEGV_WORKAROUND), 1)
	EXTRA_COSIM_CFLAGS += -DCOSIM_SIGSEGV_WORKAROUND
endif

###############################################################################

# Setup the necessary paths for all python scripts to find all other relevant modules.
export PYTHONPATH := $(shell python3 -c 'from scripts.setup_imports import get_pythonpath; get_pythonpath()')

# We run the 'create_metadata' step in this top-level makefile, so the sub-make
# invocations can query the generated metadata objects. Since the targets/dependencies
# are extracted from this metadata, it must be query-able in the makefile 'immediate' stage.
.PHONY: run
run:
	@env PYTHONPATH=$(PYTHONPATH) python3 ./scripts/metadata.py \
	  --op "create_metadata" \
	  --dir-metadata $(METADATA-DIR) \
	  --dir-out $(OUT-DIR) \
	  --args-list "\
	  SEED=$(SEED) WAVES=$(WAVES) COV=$(COV) SIMULATOR=$(SIMULATOR) \
	  ISS=$(ISS) TEST=$(TEST) VERBOSE=$(VERBOSE) ITERATIONS=$(ITERATIONS) \
	  SIGNATURE_ADDR=$(SIGNATURE_ADDR) IBEX_CONFIG=$(IBEX_CONFIG) \
	  RV32ZC=$(RV32ZC) \
	  DUT_COV_RTL_PATH=$(DUT_COV_RTL_PATH)"
	@$(MAKE) --file wrapper.mk --environment-overrides --no-print-directory $(GOAL)

# Run a wrapper.mk goal using already-created metadata.
#
# This is intended for external flows, such as the Snippy CMake flow, where
# metadata is created once by an earlier Ibex Make invocation and many simulator
# runs are launched afterwards. It preserves the top-level Makefile derived
# variables such as OUT-DIR, METADATA-DIR and PYTHONPATH, but avoids calling
# metadata.py --op create_metadata for every individual run.
.PHONY: run_existing_metadata
run_existing_metadata:
	@test -f $(METADATA-DIR)/metadata.pickle || \
	  (echo "Metadata not found: $(METADATA-DIR)/metadata.pickle. Run make run GOAL=rtl_tb_compile first."; false)
	@$(MAKE) --file wrapper.mk --environment-overrides --no-print-directory $(GOAL)

###############################################################################

# This is the top-level output directory. Everything we generate goes in
# here.
OUT := out

# Derived directories from $(OUT), used for stuff that's built once or
# stuff that gets run for each seed, respectively. Using OUT-DIR on
# the way avoids ugly double slashes if $(OUT) happens to end in a /.
export OUT-DIR      := $(dir $(OUT)/)
export METADATA-DIR := $(OUT-DIR)metadata

# riscv-dv extension directory
export EXT_DIR             := riscv_dv_extension

###############################################################################
# Snippy CMake flow
#
# The Snippy flow is implemented in CMake under snippy_cmake/. This Makefile
# block is intentionally a thin bridge:
#
#   Ibex Make knobs  ->  CMake cache variables  ->  Snippy CMake flow
#
# Toolchain and Spike variables are shared with the normal Ibex flow:
#
#   RISCV_GCC
#   RISCV_OBJCOPY
#   SPIKE_PATH
#   PKG_CONFIG_PATH
#
# Snippy runs write their standard Ibex-compatible runtime artifacts into
# $(OUT-DIR), so later Ibex coverage goals can consume them together with
# normal riscv-dv results.

# Comma-separated list of Snippy YAML layouts to run, for example:
#
#   SNIPPY_TEST="layout_arith, jalr, rem_div"
#
# Empty means: use the CMake flow default selection.
SNIPPY_TEST ?=

# Number of Snippy runs for each selected YAML layout.
SNIPPY_ITERATIONS ?= 1

# Directory with Snippy YAML layout files.
# Relative paths are resolved by CMake from dv/uvm/core_ibex.
SNIPPY_YAML_DIR ?= snippy/yaml_tests

# Placeholder metadata test name used by the Snippy CMake flow when creating
# Ibex metadata. Keep this separate from TEST so normal riscv-dv Make runs can
# keep using TEST=all or any user-selected riscv-dv test.
SNIPPY_METADATA_TEST ?= snippy_func_test

# Use snippy/urg_exclude/urg_exclude_all.txt during VCS/URG coverage merge.
USE_URG_EXCLUDE ?= ON

# CMake source and build directories for the Snippy flow.
#
# CMakeLists.txt is expected to live in this core_ibex directory and include the
# implementation files from snippy_cmake/.
SNIPPY_CMAKE_SOURCE_DIR ?= $(CURDIR)
SNIPPY_CMAKE_BUILD_DIR  ?= $(OUT-DIR)snippy_cmake_build

# Do not let the top-level Ibex VERBOSE=0 leak into CMake-generated Makefiles:
# for them, any non-empty VERBOSE value enables command echoing. Pass VERBOSE=1
# to the native build tool only when the user explicitly requested it.
SNIPPY_CMAKE_BUILD_NATIVE_ARGS := --no-print-directory
ifeq ($(VERBOSE),1)
SNIPPY_CMAKE_BUILD_NATIVE_ARGS += VERBOSE=1
endif

.PHONY: configure_snippy
configure_snippy:
	cmake -S $(SNIPPY_CMAKE_SOURCE_DIR) -B $(SNIPPY_CMAKE_BUILD_DIR) \
	  -DOUT=$(abspath $(OUT-DIR)) \
	  -DSEED=$(SEED) \
	  -DWAVES=$(WAVES) \
	  -DCOV=$(COV) \
	  -DSIMULATOR=$(SIMULATOR) \
	  -DISS=$(ISS) \
	  -DTEST=$(SNIPPY_METADATA_TEST) \
	  -DIBEX_CONFIG=$(IBEX_CONFIG) \
	  -DRV32ZC=$(RV32ZC) \
	  -DSIGNATURE_ADDR=$(SIGNATURE_ADDR) \
	  -DRISCV_GCC="$(RISCV_GCC)" \
	  -DRISCV_OBJCOPY="$(RISCV_OBJCOPY)" \
	  -DSPIKE_PATH="$(SPIKE_PATH)" \
	  -DPKG_CONFIG_PATH="$(PKG_CONFIG_PATH)" \
	  -DSNIPPY_ITERATIONS=$(SNIPPY_ITERATIONS) \
	  -DSNIPPY_TEST="$(SNIPPY_TEST)" \
	  -DYAML_DIR="$(SNIPPY_YAML_DIR)" \
	  -DUSE_URG_EXCLUDE=$(USE_URG_EXCLUDE)

.PHONY: run_snippy
run_snippy: configure_snippy
	env -u VERBOSE cmake --build $(SNIPPY_CMAKE_BUILD_DIR) --target run_all -j 60 -- $(SNIPPY_CMAKE_BUILD_NATIVE_ARGS)

.PHONY: coverage_snippy
coverage_snippy:
	@test -d $(SNIPPY_CMAKE_BUILD_DIR) || \
	  (echo "Snippy CMake build directory not found: $(SNIPPY_CMAKE_BUILD_DIR). Run make run_snippy first."; false)
	env -u VERBOSE cmake --build $(SNIPPY_CMAKE_BUILD_DIR) --target coverage -- $(SNIPPY_CMAKE_BUILD_NATIVE_ARGS)

###############################################################################

.PHONY: clean
clean:
	rm -rf $(OUT-DIR)
	rm -f $(EXT_DIR)/riscv_core_setting.sv

###############################################################################
