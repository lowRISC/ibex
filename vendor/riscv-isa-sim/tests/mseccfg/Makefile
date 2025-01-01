# Makefile for program model example

XLEN ?= 32
VLEN ?= 1024
RISCV_TOOL ?= ~/lowrisc-toolchain-gcc-rv32imcb-20220524-1/bin/
SPIKE_PATH ?= ~/riscv-isa-sim/build
SAIL_EMULATOR_PATH = /home/scratch.soberl_maxwell/arch1/sail_2021/sail-riscv/c_emulator

SSP_OPT ?=
PERF ?= 0

LIB_PATH = .
# ../ctests/nvrvv_lib.c
COMMON_FILES = \
	$(LIB_PATH)/crt.S \
	$(LIB_PATH)/syscalls.c

TEST_PATH = ./gengen_src/outputs

ALL_TEST ?= $(basename $(notdir $(wildcard $(TEST_PATH)/*.c)))
DEV_TEST = test_pmp_csr_1_lock01_rlb0_mmwp0_mml0_sec_04
OBJECTS ?= $(ALL_TEST)
# NEVER enable 'C' because pc + 4 is used in test code.
# -ffast-math -fno-common -fno-builtin-printf
CFLAGS = -march=rv$(XLEN)imafd -O2 -I . -I ./$(LIB_PATH) -I ../softfloat -I ../riscv \
	-fno-builtin-printf -fdata-sections -fno-section-anchors $(SSP_OPT) -DPRINTF_SUPPORTED=1
LDFLAGS = -mcmodel=medany -static -nostdlib -nostartfiles -lm -lgcc \
	-T $(LIB_PATH)/mseccfg_test.ld  -Wl,-M -Wl,-Map=link.log

# must enable 'C', maybe used in pk
# 8M for TCM memories
# 16M for L2 memories
SIM_ISA = --isa=RV$(XLEN)IMAFDC

default:
	@echo "make gen, to generate all test cases with gengen"
	@echo "make run, to run all test cases"
	@echo "set OBJECTS variant to select specified test case"

gen:
	cd gengen_src; $(MAKE); $(MAKE) gen;

$(OBJECTS):
	@$(RISCV_TOOL)/riscv$(XLEN)-unknown-elf-gcc $(CFLAGS) $(TEST_PATH)/$@.c $(COMMON_FILES) $(LDFLAGS) -o a.out 
	@echo Running $(TEST_PATH)/$@.c - command - $(RISCV_TOOL)/riscv$(XLEN)-unknown-elf-gcc $(CFLAGS) $(TEST_PATH)/$@.c $(COMMON_FILES) $(LDFLAGS) -o a.out
	@$(RISCV_TOOL)/riscv$(XLEN)-unknown-elf-objdump -d a.out > a.ss
	@$(RISCV_TOOL)/riscv$(XLEN)-unknown-elf-objdump --disassemble=target_foo a.out >> a.ss
ifeq ($(PERF), 0)
	$(SPIKE_PATH)/spike $(SIM_ISA) -m0x100000:0x200000 a.out
#	$(SAIL_EMULATOR_PATH)/riscv_sim_RV64 --enable-pmp -V a.out > tmp.log 2>&1; grep SUCCESS tmp.log
#	@! grep FAILURE tmp.log
#	$(RISCV_TOOL)/spike $(SIM_ISA) -l a.out > $@_pc.log 2>&1
#	sed -i '0,/ nop/d' $@_pc.log
#	sed -i '/ nop/q' $@_pc.log
endif

run: $(OBJECTS)

clean:
	rm *.s *.o *.i *.ss *.out *.log *.bin

log:
	$(SPIKE_PATH)/spike $(SIM_ISA) -m0x100000:0x200000 -l a.out > 1.log 2>&1
	$(SAIL_EMULATOR_PATH)/riscv_sim_RV64 --enable-pmp a.out > 2.log 2>&1

env:
	echo $(ALL_TEST)


.PHONY: gen $(OBJECTS) clean
