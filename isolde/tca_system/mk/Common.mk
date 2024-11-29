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


num_cores := $(shell nproc)
num_cores_half := $(shell echo "$$(($(num_cores) / 2))")

PRJ_HOME      := $(shell git rev-parse --show-toplevel)/isolde/tca_system
CORE_V_VERIF  := $(PRJ_HOME)
TBSRC_HOME    := $(PRJ_HOME)/tb
TBSRC_CORE    := $(TBSRC_HOME)/core


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


TEST_FILES        ?= $(filter %.c %.S,$(wildcard  $(TEST_SRC_DIR)/*))
# Optionally use linker script provided in test directory
# this must be evaluated at access time, so ifeq/ifneq does
# not get parsed correctly
TEST_RESULTS_LD = $(addprefix $(SIM_TEST_PROGRAM_RESULTS)/, link.ld)
TEST_LD         = $(addprefix $(TEST_SRC_DIR)/, link.ld)

LD_LIBRARY 	= $(if $(wildcard $(TEST_RESULTS_LD)),-L $(SIM_TEST_PROGRAM_RESULTS),$(if $(wildcard $(TEST_LD)),-L $(TEST_SRC_DIR),))
LD_FILE 	= $(if $(wildcard $(TEST_RESULTS_LD)),$(TEST_RESULTS_LD),$(if $(wildcard $(TEST_LD)),$(TEST_LD),$(BSP)/link.ld))



BSP                                  = $(CORE_V_VERIF)/bsp


RISCV_CFLAGS += -I $(CORE_V_VERIF)
RISCV_CFLAGS += -I $(BSP)
RISCV_CFLAGS += -I $(TEST_SRC_DIR)
RISCV_CFLAGS += -I $(TEST_SRC_DIR)/inc
RISCV_CFLAGS += -I $(TEST_SRC_DIR)/utils
RISCV_CFLAGS += -DUSE_BSP
#RISCV_CFLAGS += -DCV32E40X 
RISCV_CFLAGS += -DIBEX 


%.elf:
	@echo "$(BANNER)"
	@echo "* Compiling $@"
	@echo "$(BANNER)"
	mkdir -p $(SIM_BSP_RESULTS)
	cp $(BSP)/Makefile $(SIM_BSP_RESULTS)
	make -C $(SIM_BSP_RESULTS) \
		APP_FILES=$(TEST_FILES)    \
		VPATH=$(TEST_SRC_DIR):$(BSP) \
		RISCV=$(RISCV) \
		RISCV_PREFIX=$(RISCV_PREFIX) \
		RISCV_EXE_PREFIX=$(RISCV_EXE_PREFIX) \
		RISCV_MARCH=$(RISCV_MARCH) \
		RISCV_CC=$(RISCV_CC) \
		RISCV_CFLAGS="$(RISCV_CFLAGS)" \
		LD_FILE=$(BSP)/link.ld \
		$@


%.hex: %.elf
	@echo "$(BANNER)"
	@echo "* Generating $@, readelf and objdump files"
	@echo "$(BANNER)"
	$(RISCV_EXE_PREFIX)objcopy -O verilog \
		$< \
		$@
	python $(SCRIPTS_DIR)/addr_offset.py  $@  $*-m.hex 0x00100000
	python $(SCRIPTS_DIR)/addr_offset.py  $@  $*-d.hex 0x00100000
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




clean-bsp:
#	make -C $(BSP) clean
	rm -rf $(SIM_BSP_RESULTS)

clean-test-programs: clean-bsp
	find $(PRJ_HOME)/../sw/simple_system -name "*.o"       -delete
	find  $(PRJ_HOME)/../sw/simple_system -name "*.hex"     -delete
	find  $(PRJ_HOME)/../sw/simple_system -name "*.elf"     -delete
	find  $(PRJ_HOME)/../sw/simple_system -name "*.d"     -delete
	find  $(PRJ_HOME)/../sw/simple_system -name "*.map"     -delete
	find  $(PRJ_HOME)/../sw/simple_system -name "*.readelf" -delete
	find  $(PRJ_HOME)/../sw/simple_system -name "*.objdump" -delete
	find  $(PRJ_HOME)/../sw/simple_system -name "*.headers" -delete
	find  $(PRJ_HOME)/../sw/simple_system -name "corev_*.S" -delete
	find  $(PRJ_HOME)/../sw/simple_system -name "*.itb" -delete	

