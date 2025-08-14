###############################################################################
#
# Copyleft  2024 ISOLDE
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
## redmule config
REDMULE_ROOT_DIR :=$(shell bender path redmule)

num_cores := $(shell nproc)
num_cores_half := $(shell echo "$$(($(num_cores) / 2))")

ifeq ($(PE), redmule)
    TEST_SRC_DIR       = $(REDMULE_ROOT_DIR)/sw
	TEST_FILES         = $(TEST).c
endif

ifeq ($(PE), onnx)
    TEST_SRC_DIR       = $(ROOT_DIR)/isolde/sw/onnx
	TEST_FILES         = $(TEST).c
endif

## debuger module config
ifeq ($(DBG_MODULE), 1)
    RV_DM_C_FLAGS += -DRV_DM_TEST
else
    RV_DM_C_FLAGS += 
endif


CORE_V_VERIF  := $(mkfile_path)


#
SCRIPTS_DIR     = $(ROOT_DIR)/isolde/scripts
###############################################################################
##
RISCV_PREFIX     = $(CV_SW_PREFIX)
RISCV_EXE_PREFIX = $(CV_SW_TOOLCHAIN)/bin/$(RISCV_PREFIX)

RISCV_MARCH      =  $(CV_SW_MARCH)
RISCV_CC_SUFFIX  =  $(CV_SW_CC_SUFFIX)
RISCV_CFLAGS     += $(RV_DM_C_FLAGS)


TEST_FILES        ?= $(filter %.c %.S,$(wildcard  $(TEST_SRC_DIR)/*))
# Optionally use linker script provided in test directory
# this must be evaluated at access time, so ifeq/ifneq does
# not get parsed correctly
TEST_RESULTS_LD = $(addprefix $(SIM_TEST_PROGRAM_RESULTS)/, link.ld)
TEST_LD         = $(addprefix $(TEST_SRC_DIR)/, link.ld)

LD_LIBRARY 	= $(if $(wildcard $(TEST_RESULTS_LD)),-L $(SIM_TEST_PROGRAM_RESULTS),$(if $(wildcard $(TEST_LD)),-L $(TEST_SRC_DIR),))
LD_FILE 	= $(if $(wildcard $(TEST_RESULTS_LD)),$(TEST_RESULTS_LD),$(if $(wildcard $(TEST_LD)),$(TEST_LD),$(BSP)/link.ld))



BSP                                  = $(CORE_V_VERIF)/bsp
SIM_BSP_RESULTS                      = $(CORE_V_VERIF)/sw/build/bsp

RISCV_CFLAGS += -I $(CORE_V_VERIF)
#RISCV_CFLAGS += -I $(BSP)
RISCV_CFLAGS += -I $(TEST_SRC_DIR)
RISCV_CFLAGS += -I $(TEST_SRC_DIR)/inc
RISCV_CFLAGS += -I $(TEST_SRC_DIR)/utils
RISCV_CFLAGS += -DUSE_BSP
#RISCV_CFLAGS += -DCV32E40X 
RISCV_CFLAGS += -DIBEX 
RISCV_CFLAGS += $(TEST_CFLAGS)

%.elf:
	@echo "**** sw-build.mk compiling:"
	@echo "**** $@"
	@echo "**** TEST_FILES = $(TEST_FILES) "
	@echo "$(BANNER)"
	mkdir -p $(SIM_BSP_RESULTS)
	cp $(BSP)/Makefile $(SIM_BSP_RESULTS)
	make -C $(SIM_BSP_RESULTS) \
		APP_FILES="$(TEST_FILES)"    \
		VPATH=$(TEST_SRC_DIR):$(BSP) \
		CV_SW_TOOLCHAIN=$(CV_SW_TOOLCHAIN) \
		RISCV_PREFIX=$(RISCV_PREFIX) \
		RISCV_CC_SUFFIX=$(RISCV_CC_SUFFIX) \
		RISCV_MARCH=$(RISCV_MARCH) \
		RISCV_CFLAGS="$(RISCV_CFLAGS)" \
		LD_FILE=$(BSP)/link.ld \
		$@


%.hex: %.elf
	@echo "$(BANNER)"
	@echo "* Generating $@, readelf and objdump files"
	@echo "$(BANNER)"
	$(CV_SW_TOOLCHAIN)/bin/riscv32-unknown-elf-objcopy -O verilog \
		$< \
		$@
	python $(SCRIPTS_DIR)/addr_offset.py   $@  $*-m.hex 0x00100000
	python $(SCRIPTS_DIR)/addr_offset.py   $@  $*-d.hex 0x00100000
#	python $(SCRIPTS_DIR)/hex2bin_split.py $@  $*-instr.bin $*-data.bin
	python $(SCRIPTS_DIR)/hex2ihex_split.py  --input $@ \
											--instr-base 0x00100000 --instr-size 0x8000 \
											--data-base  0x00110000 --data-size 0x30000 \
											--instr-out instr.hex \
											--data-out data.hex \
											--verbose
	$(CV_SW_TOOLCHAIN)/bin/riscv32-unknown-elf-readelf -a $< > $*.readelf
	$(CV_SW_TOOLCHAIN)/bin/riscv32-unknown-elf-objdump   \
		-fhSD \
		-M no-aliases \
		-M numeric \
		-S \
		$*.elf > $*.objdump









clean-bsp:
#	make -C $(BSP) clean
	rm -rf $(SIM_BSP_RESULTS)

clean-test-programs: clean-bsp
	find $(CORE_V_VERIF)/../sw -name "*.o"       -delete
	find  $(CORE_V_VERIF)/../sw -name "*.hex"     -delete
	find  $(CORE_V_VERIF)/../sw -name "*.elf"     -delete
	find  $(CORE_V_VERIF)/../sw -name "*.d"     -delete
	find  $(CORE_V_VERIF)/../sw -name "*.map"     -delete
	find  $(CORE_V_VERIF)/../sw -name "*.readelf" -delete
	find  $(CORE_V_VERIF)/../sw -name "*.objdump" -delete
	find  $(CORE_V_VERIF)/../sw -name "*.headers" -delete
	find  $(CORE_V_VERIF)/../sw -name "corev_*.S" -delete
	find  $(CORE_V_VERIF)/../sw -name "*.itb" -delete	

###ISOLDE specific
ifneq ($(filter redmule_%,$(TEST)),)

golden:
	make -C $(REDMULE_ROOT_DIR) $@
	make -C $(TEST_SRC_DIR) $@

else

golden:
	@echo "Skipped, redmule unrelated"

endif



.PHONY: test-build $(test-program) clean $(TEST_BIN_DIR)

$(TEST_BIN_DIR):
	mkdir -p $@


$(test-program).hex: $(test-program).elf
test-build: $(TEST_BIN_DIR) $(test-program).hex

test-clean: clean-bsp
	rm -f $(test-program)*
	rm -fr $(TEST_BIN_DIR) 
	rm -fr $(SIM_BSP_RESULTS)
	-find $(TEST_SRC_DIR) -name "*.o"       -delete



clean: veri-clean test-clean-programs
	rm -fr $(BUILD_DIR) $(TEST_BIN_DIR) logs 
	rm -f *.log *.csv

clean-hw:
	rm -fr $(BUILD_DIR) logs
