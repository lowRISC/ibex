###############################################################################
#
# Copyleft  2024
# Copyright 2020 OpenHW Group
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
###############################################################################
#
# Common code for simulation Makefiles.
#
###############################################################################
#
# Copyright 2019 Claire Wolf
# Copyright 2019 Robert Balas
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
# REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
# INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
# LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
# OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
# PERFORMANCE OF THIS SOFTWARE.
#
# Original Author: Robert Balas (balasr@iis.ee.ethz.ch)
#
###############################################################################
##
###############################################################################
CV_CORE      ?= CV32E40P

num_cores := $(shell nproc)
num_cores_half := $(shell echo "$$(($(num_cores) / 2))")

PRJ_HOME      := $(shell git rev-parse --show-toplevel)/isolde/lca_system
CORE_V_VERIF  := $(PRJ_HOME)
TBSRC_HOME    := $(PRJ_HOME)/tb
TBSRC_CORE    := $(TBSRC_HOME)/core
# TBSRC_VERI    := $(TBSRC_CORE)/tb_top_verilator.sv \
#                  $(TBSRC_CORE)/cv32e40p_tb_wrapper.sv \
#                  $(TBSRC_CORE)/tb_riscv/riscv_rvalid_stall.sv \
#                  $(TBSRC_CORE)/tb_riscv/riscv_gnt_stall.sv \
#                  $(TBSRC_CORE)/mm_ram.sv \
#                  $(TBSRC_CORE)/dp_ram.sv


CV_CORE_LC     = $(shell echo $(CV_CORE) | tr A-Z a-z)
CV_CORE_UC     = $(shell echo $(CV_CORE) | tr a-z A-Z)

CV_CORE_PKG           :=  
CV_CORE_MANIFEST    ?= $(CV_CORE_PKG)/cv32e40p_manifest.flist
export DESIGN_RTL_DIR = $(CV_CORE_PKG)/rtl


#
SCRIPTS_DIR     = $(REDMULE_ROOT_DIR)/scripts
###############################################################################
##
RISCV            = $(CV_SW_TOOLCHAIN)
RISCV_PREFIX     = $(CV_SW_PREFIX)
RISCV_EXE_PREFIX = $(RISCV)/bin/$(RISCV_PREFIX)

RISCV_MARCH      =  $(CV_SW_MARCH)
RISCV_CC         =  $(CV_SW_CC)
RISCV_CFLAGS     += 

#CFLAGS ?= -Os -g -static -mabi=ilp32 -march=$(RISCV_MARCH) -Wall -pedantic $(RISCV_CFLAGS)

#TEST_FILES        = $(filter %.c %.S,$(wildcard  $(TEST_TEST_DIR)/*))
# Optionally use linker script provided in test directory
# this must be evaluated at access time, so ifeq/ifneq does
# not get parsed correctly
TEST_RESULTS_LD = $(addprefix $(SIM_TEST_PROGRAM_RESULTS)/, link.ld)
TEST_LD         = $(addprefix $(TEST_TEST_DIR)/, link.ld)

LD_LIBRARY 	= $(if $(wildcard $(TEST_RESULTS_LD)),-L $(SIM_TEST_PROGRAM_RESULTS),$(if $(wildcard $(TEST_LD)),-L $(TEST_TEST_DIR),))
LD_FILE 	= $(if $(wildcard $(TEST_RESULTS_LD)),$(TEST_RESULTS_LD),$(if $(wildcard $(TEST_LD)),$(TEST_LD),$(BSP)/link.ld))



BSP                                  = $(CORE_V_VERIF)/$(CV_CORE_LC)/bsp


RISCV_CFLAGS += -I $(CORE_V_VERIF)/$(CV_CORE_LC)
RISCV_CFLAGS += -I $(TEST_TEST_DIR)
RISCV_CFLAGS += -I $(TEST_TEST_DIR)/inc
RISCV_CFLAGS += -I $(TEST_TEST_DIR)/utils
RISCV_CFLAGS += -DUSE_BSP



%.hex: %.elf
	@echo "$(BANNER)"
	@echo "* Generating hexfile, readelf and objdump files"
	@echo "$(BANNER)"
	$(RISCV_EXE_PREFIX)objcopy -O verilog \
		$< \
		$@
	python $(SCRIPTS_DIR)/addr_offset.py  $@  $*-m.hex 0x00100000
	$(RISCV_EXE_PREFIX)readelf -a $< > $*.readelf
	$(RISCV_EXE_PREFIX)objdump \
		-fhSD \
		-M no-aliases \
		-M numeric \
		-S \
		$*.elf > $*.objdump


bsp:
	@echo "$(BANNER)"
	@echo "* Compiling the BSP"
	@echo "$(BANNER)"
	mkdir -p $(SIM_BSP_RESULTS)
	cp $(BSP)/Makefile $(SIM_BSP_RESULTS)
	make -C $(SIM_BSP_RESULTS) \
		VPATH=$(BSP) \
		RISCV=$(RISCV) \
		RISCV_PREFIX=$(RISCV_PREFIX) \
		RISCV_EXE_PREFIX=$(RISCV_EXE_PREFIX) \
		RISCV_MARCH=$(RISCV_MARCH) \
		RISCV_CC=$(RISCV_CC) \
		RISCV_CFLAGS="$(RISCV_CFLAGS)" \
		all


%.elf:
	@echo "$(BANNER)"
	@echo "* Compiling the test"
	@echo "$(BANNER)"
	mkdir -p $(SIM_BSP_RESULTS)
	cp $(BSP)/Makefile $(SIM_BSP_RESULTS)
	make -C $(SIM_BSP_RESULTS) \
		APP_FILES=$(TEST_FILES)    \
		VPATH=$(TEST_TEST_DIR):$(BSP) \
		RISCV=$(RISCV) \
		RISCV_PREFIX=$(RISCV_PREFIX) \
		RISCV_EXE_PREFIX=$(RISCV_EXE_PREFIX) \
		RISCV_MARCH=$(RISCV_MARCH) \
		RISCV_CC=$(RISCV_CC) \
		RISCV_CFLAGS="$(RISCV_CFLAGS)" \
		LD_FILE=$(BSP)/link.ld \
		$@


clean-bsp:
#	make -C $(BSP) clean
	rm -rf $(SIM_BSP_RESULTS)

clean-test-programs: clean-bsp
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name "*.o"       -delete
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name "*.hex"     -delete
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name "*.elf"     -delete
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name "*.map"     -delete
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name "*.readelf" -delete
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name "*.objdump" -delete
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name "*.headers" -delete
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name "corev_*.S" -delete
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name "*.itb" -delete	

