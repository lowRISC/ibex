CV_SW_TOOLCHAIN  ?= /opt/riscv
RISCV            ?= $(CV_SW_TOOLCHAIN)
RISCV_EXE_PREFIX ?= $(RISCV)/bin/riscv32-unknown-elf-
RISCV_GCC = $(RISCV_EXE_PREFIX)gcc
RISCV_AR = $(RISCV_EXE_PREFIX)ar
SRC = crt0.S simple_system_common.c startup.c tinyprintf.c
OBJ = crt0.o simple_system_common.o startup.o tinyprintf.o
LIBCV-VERIF = libcv-verif.a 
TINY_PRINTF_FLAGS += -DTINYPRINTF_DEFINE_TFP_PRINTF
TINY_PRINTF_FLAGS += -DTINYPRINTF_DEFINE_TFP_SPRINTF


CFLAGS ?= -Os -g -static -mabi=ilp32 -march=$(CV_SW_MARCH)  $(TINY_PRINTF_FLAGS)  -ffunction-sections -fdata-sections -Wall -pedantic

all: $(LIBCV-VERIF)

$(LIBCV-VERIF): $(OBJ) 
	$(RISCV_AR) rcs $@ $(OBJ)

%.o : %.c
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@
	
%.o : %.S
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJ) $(LIBCV-VERIF)


vars:
	@echo "make bsp variables:"
	@echo "   CV_SW_TOOLCHAIN  = $(CV_SW_TOOLCHAIN)"
	@echo "   CV_SW_MARCH      = $(CV_SW_MARCH)"
	@echo "   RISCV            = $(RISCV)"
	@echo "   RISCV_EXE_PREFIX = $(RISCV_EXE_PREFIX)"
	@echo "   RISCV_GCC        = $(RISCV_GCC)"
	@echo "   RISCV_MARCH      = $(RISCV_MARCH)"

