# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

COMMON_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))

COMMON_SRCS = $(wildcard $(COMMON_DIR)/*.c)
INCS := -I$(COMMON_DIR)


TARGET      := riscv32
ARCH        := rv32g
RISCV_ABI   := ilp32

RISCV_WARNINGS += -Wunused-variable -Wall -Wextra -Wno-unused-command-line-argument # -Werror

LLVM_FLAGS     ?= --target=$(TARGET) -march=$(ARCH)  -menable-experimental-extensions -mabi=$(RISCV_ABI) -mno-relax 
RISCV_FLAGS    ?= $(LLVM_FLAGS) -mcmodel=medany  -O3 -ffast-math  -g $(RISCV_WARNINGS)
RISCV_CCFLAGS  ?= $(RISCV_FLAGS) -ffunction-sections -fdata-sections  -std=gnu99 -nostdlib -nostartfiles
RISCV_CXXFLAGS ?= $(RISCV_FLAGS) -ffunction-sections -fdata-sections
RISCV_LDFLAGS  ?= -static -nostdlib 

LINKER_SCRIPT ?= $(COMMON_DIR)/link.ld

CFLAGS ?= -march=$(ARCH) -mabi=ilp32 -static -mcmodel=medany -Wall -g -O3\
	-fvisibility=hidden -nostdlib -nostartfiles -ffreestanding $(PROGRAM_CFLAGS)

ifdef PROGRAM
PROGRAM_C := $(PROGRAM).c
endif

SRCS = $(COMMON_SRCS) $(PROGRAM_C) $(EXTRA_SRCS)

C_SRCS = $(filter %.c, $(SRCS))
ASM_SRCS = $(filter %.S, $(SRCS))

CC := $(LLVM_TOOLCHAIN)/clang
LD := $(LLVM_TOOLCHAIN)/riscv32-unknown-elf-ld
#LD := $(LLVM_TOOLCHAIN)/ld.lld
#LD := $(GCC_TOOLCHAIN)/riscv32-unknown-elf-gcc


#OBJCOPY := $(LLVM_TOOLCHAIN)/llvm-objcopy
OBJDUMP := $(GCC_TOOLCHAIN)/riscv32-unknown-elf-objdump
#OBJDUMP := $(LLVM_TOOLCHAIN)/llvm-objdump


CRT ?= $(COMMON_DIR)/crt0.S

	 


OBJS := ${C_SRCS:.c=.o} ${ASM_SRCS:.S=.o} ${CRT:.S=.o}
DEPS = $(OBJS:%.o=%.d)

ifdef PROGRAM
OUTFILES := $(PROGRAM).elf 
else
OUTFILES := $(OBJS)
endif

all: $(OUTFILES)

ifdef PROGRAM
$(PROGRAM).elf: $(OBJS) $(LINKER_SCRIPT)
#	$(LD) $(CFLAGS) -T $(LINKER_SCRIPT) $(OBJS) -o $@ $(LIBS)
	$(LD) $(RISCV_LDFLAGS)  -Map $@.map -T $(LINKER_SCRIPT) $(OBJS) -o $@ $(LIBS)
	$(OBJDUMP) -dh  $@ >$@.headers
	

.PHONY: disassemble
disassemble: $(PROGRAM).dis
endif

%.dis: %.elf
	$(OBJDUMP) -fhSD $^ > $@

# Note: this target requires the srecord package to be installed.
# XXX: This could be replaced by objcopy once
# https://sourceware.org/bugzilla/show_bug.cgi?id=19921
# is widely available.
%.vmem: %.bin
	srec_cat $^ -binary -offset 0x0000 -byte-swap 4 -o $@ -vmem

%.bin: %.elf
	$(OBJCOPY) -O binary $^ $@

%.o: %.c
	$(CC) -c $(RISCV_CCFLAGS) $(INCS) -o $@ $<
# Rule to compile C to assembly
%.s: %.c
	$(CC) -S $(RISCV_CCFLAGS) $(INCS) -o $@ $<


%.o: %.S
	$(CC) -c $(RISCV_CCFLAGS) $(INCS) -o $@ $<

clean:
	$(RM) -f $(OBJS) $(DEPS)
	rm -f *.bin *.vmem *.elf *.headers

distclean: clean
	$(RM) -f $(OUTFILES)
