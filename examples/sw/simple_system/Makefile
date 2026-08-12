# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

COSIM ?= lowrisc:ibex:ibex_simple_system_cosim
LINKER ?= ./common/link.ld
CFLAGS := -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles
INCLUDE_FILES := -I../../../vendor/riscv-test-env/ \
		 -I../../../vendor/riscv-test-env/p/ \
		 -I../../../vendor/riscv-tests/isa/macros/scalar/ \
		 -I../../../dv/uvm/core_ibex/directed_tests \
		 -T$(LINKER) \
		 -DSIMPLE_SYSTEM

DIRECTED_TESTS_PATH ?= ../../../dv/uvm/core_ibex/directed_tests
TEST_PATH ?= $(DIRECTED_TESTS_PATH)/empty/empty.S
TEST := $(shell basename $(TEST_PATH) .S)

RISCV_OBJDUMP := $(patsubst %-gcc,%-,$(RISCV_GCC))objdump

run: build_rtl compile_prog run_prebuilt_rtl

build_rtl:
	fusesoc --cores-root=../../../ run --target=sim --setup --build $(COSIM) --RV32E=0 --RV32M=ibex_pkg::RV32MFast --PMPEnable=1

compile_prog:
	$(RISCV_GCC) $(CFLAGS) $(INCLUDE_FILES) -o $(TEST).elf $(TEST_PATH)
	$(RISCV_OBJDUMP) -DS $(TEST).elf > $(TEST).dis

run_prebuilt_rtl: compile_prog run_precompiled_test

run_precompiled_test:
	./build/lowrisc_ibex_ibex_simple_system_cosim_0/sim-verilator/Vibex_simple_system --meminit=ram,$(TEST).elf

clean:
	$(RM) -f *.o *.elf *.dis *.log
