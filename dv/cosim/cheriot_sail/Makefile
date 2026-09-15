# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Step 1 build target: compile cheriot-sail generated C into a shared library
# suitable for in-process DPI cosim use.
#
# Must be run inside a shell providing: gcc, gmp, zlib (e.g. the verification
# repo's `nix develop .#eda_shell`, layered with a gcc since eda_shell has none
# on PATH itself -- see the root Makefile's build-cheriotsail-lib).
#
# Usage: normally invoked from the verification repo root, which supplies
# CHERIOT_SAIL_DIR:
#   make build-cheriotsail-lib
#
# Standalone (from this directory):
#   make [CHERIOT_SAIL_DIR=/path/to/cheriot-sail] [SAIL_LIB_DIR=/path/to/sail/lib]

# ---------------------------------------------------------------------------
# Paths
# ---------------------------------------------------------------------------

# Default to ../cheriot-sail-model, a sibling of this directory under
# ibex/dv/cosim/. This is a plain, untracked copy of the SamuelRiedel/
# cheriot-sail fork (+ its patched sail-riscv) taken from an old
# TestRIG-private checkout -- TestRIG-private itself is no longer used.
# Must not be an absolute developer-specific path: this Makefile is shared,
# and a hardcoded /home/<user>/... breaks every other machine and CI.
CHERIOT_SAIL_DIR ?= $(abspath $(CURDIR)/../cheriot-sail-model)
SAIL_RISCV_DIR   := $(CHERIOT_SAIL_DIR)/sail-riscv
GEN_C_DIR        := $(CHERIOT_SAIL_DIR)/generated_definitions/c

# Sail lib dir (sail -dir prints the sail installation root; lib/ is under it,
# but only for a sail matching the pre-generated MODEL_C below -- the current
# `lowrisc_sail` package, from github:lowrisc/sail?ref=ast_translate, is a
# newer release whose runtime headers, e.g. sail_config.h, don't match).
# Default to a copy of the working sail 0.19.1 (rems-project/sail@31cd072)
# runtime lib vendored alongside cheriot-sail-model; override for a different sail.
SAIL_LIB_DIR ?= $(abspath $(CURDIR)/../sail-0.19.1-runtime)

# ---------------------------------------------------------------------------
# Sources
# ---------------------------------------------------------------------------

# Generated Sail→C model (RVFI-DII variant)
MODEL_C := $(GEN_C_DIR)/riscv_rvfi_model_RV32.c

# Sail C runtime (plain .c files — no pre-built library needed)
SAIL_RUNTIME_SRCS := \
    $(SAIL_LIB_DIR)/sail.c \
    $(SAIL_LIB_DIR)/rts.c \
    $(SAIL_LIB_DIR)/elf.c \
    $(SAIL_LIB_DIR)/sail_failure.c

# cheriot-sail platform support (no main — riscv_sim.c is intentionally excluded)
PLATFORM_SRCS := \
    $(SAIL_RISCV_DIR)/c_emulator/riscv_prelude.c \
    $(SAIL_RISCV_DIR)/c_emulator/riscv_platform_impl.c \
    $(SAIL_RISCV_DIR)/c_emulator/riscv_platform.c

# DPI wrapper (compiled as C++ with Sail headers already on the path)
DPI_SRCS := cheriot_sail_cosim_dpi.cc

ALL_SRCS := $(MODEL_C) $(PLATFORM_SRCS) $(SAIL_RUNTIME_SRCS) $(DPI_SRCS)

# ---------------------------------------------------------------------------
# Flags
# ---------------------------------------------------------------------------

CC     := gcc
CXX    := g++
CFLAGS := -O2 -fPIC \
    -DRVFI_DII \
    -DNO_BOOT_ROM=1 \
    -I$(SAIL_LIB_DIR) \
    -I$(SAIL_RISCV_DIR)/c_emulator \
    -I$(GEN_C_DIR) \
    $(shell pkg-config --cflags gmp) \
    $(shell pkg-config --cflags zlib)
CXXFLAGS := $(CFLAGS) -std=c++14

# -L paths for gmp/zlib are required in a nix devShell (they live under
# non-standard nix-store paths, not the linker's default search path).
LDFLAGS := -shared \
    $(shell pkg-config --libs gmp) \
    $(shell pkg-config --libs zlib) \
    -lpthread -ldl -lstdc++

OUT := libcheriotsail_rvfi.so

# ---------------------------------------------------------------------------
# Targets
# ---------------------------------------------------------------------------

.PHONY: all clean

all: $(OUT)

# If the generated .c is missing, regenerate it via the cheriot-sail Makefile.
# This requires sail on PATH (provided by the TestRIG nix develop shell).
$(MODEL_C):
	$(MAKE) -C $(CHERIOT_SAIL_DIR) generated_definitions/c/riscv_rvfi_model_RV32.c

BUILD_DIR := build

C_OBJS   := $(patsubst %.c,$(BUILD_DIR)/%.o,$(notdir $(filter %.c,$(ALL_SRCS))))
CXX_OBJS := $(patsubst %.cc,$(BUILD_DIR)/%.o,$(notdir $(filter %.cc,$(ALL_SRCS))))
ALL_OBJS := $(C_OBJS) $(CXX_OBJS)

$(BUILD_DIR):
	mkdir -p $@

define c_rule
$(BUILD_DIR)/$(notdir $(patsubst %.c,%.o,$(1))): $(1) | $(BUILD_DIR)
	$$(CC) $$(CFLAGS) -c $$< -o $$@
endef

define cxx_rule
$(BUILD_DIR)/$(notdir $(patsubst %.cc,%.o,$(1))): $(1) | $(BUILD_DIR)
	$$(CXX) $$(CXXFLAGS) -c $$< -o $$@
endef

$(foreach src,$(filter %.c,$(ALL_SRCS)),$(eval $(call c_rule,$(src))))
$(foreach src,$(filter %.cc,$(ALL_SRCS)),$(eval $(call cxx_rule,$(src))))

$(OUT): $(ALL_OBJS)
	$(CXX) $(LDFLAGS) $^ -o $@
	@echo "Built: $@"
	@nm $@ | grep -c "zrvfi_get_cheri_data" && echo "OK: zrvfi_get_cheri_data exported" || echo "WARN: zrvfi_get_cheri_data not found"
	@nm $@ | grep -c "cheriot_sail_cosim_step" && echo "OK: cheriot_sail_cosim_step exported" || echo "WARN: cheriot_sail_cosim_step not found"

clean:
	rm -rf $(OUT) $(BUILD_DIR)
