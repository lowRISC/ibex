CV_SW_TOOLCHAIN  ?= /opt/riscv
RISCV_EXE_PREFIX ?= $(CV_SW_TOOLCHAIN)/bin/riscv32-unknown-elf-
RISCV_GCC        =  $(RISCV_EXE_PREFIX)gcc
RISCV_AR         =  $(RISCV_EXE_PREFIX)ar
OBJDUMP          =  $(RISCV_EXE_PREFIX)objdump

LD_FILE ?=
# Source files
APP_FILES ?=
SRCS   += crt0.S simple_system_common.c startup.c tinyprintf.c 
SRCS   += $(APP_FILES)

SRC_C = $(filter %.c, $(SRCS))
SRC_S = $(filter %.S, $(SRCS))

# Generate object files automatically from source files
OBJS += $(SRC_S:.S=.o)
OBJS += $(SRC_C:.c=.o)

DEPS = $(OBJS:.o=.d)

# Library output
LIBCV-VERIF = libcv-verif.a

# Flags for tinyprintf
TINY_PRINTF_FLAGS += -DTINYPRINTF_DEFINE_TFP_PRINTF=1
TINY_PRINTF_FLAGS += -DTINYPRINTF_DEFINE_TFP_SPRINTF=0

# Compiler flags
CFLAGS ?= -march=$(RISCV_MARCH) -mabi=ilp32 -static -mcmodel=medany -Wall -g -O3 \
	-fvisibility=hidden -nostdlib -nostartfiles -ffreestanding $(TINY_PRINTF_FLAGS) $(RISCV_CFLAGS)

# Build the library
all: $(LIBCV-VERIF)

$(LIBCV-VERIF): $(OBJS)
	@echo '***  packing ' $(OBJS) into $(CURDIR)/$@
	$(RISCV_AR) rcs $@ $(OBJS)

# Compilation rules
%.o : %.c
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@

%.o : %.S
	$(RISCV_GCC) $(CFLAGS) -c $< -o $@

# Clean up the generated files
clean:
	rm -f $(OBJS) 
	rm -f $(DEPS)  
	rm -f $(LIBCV-VERIF)

# Print variables for debugging
vars:
	@echo "## make bsp variables:"
	@echo "   ############################"
	@echo "   CV_SW_TOOLCHAIN  = $(CV_SW_TOOLCHAIN)"       
	@echo "   RISCV_EXE_PREFIX = $(RISCV_EXE_PREFIX)"
	@echo "   RISCV_GCC        = $(RISCV_GCC)"
	@echo "   RISCV_MARCH      = $(RISCV_MARCH)"    
	     


compile: $(OBJS)
	@echo  '*** compiled: ' $(SRCS)


%.elf:  vars $(OBJS)
#	mkdir -p $(SIM_TEST_PROGRAM_RESULTS)
	@echo "*** linking $(OBJS) into $@"
	@echo "$(BANNER)"
	$(RISCV_EXE_PREFIX)$(RISCV_CC) \
		$(CFLAGS) \
		-o $@ \
		$(OBJS) \
		-T $(LD_FILE) \
#	$(CC) $(CFLAGS) -T $(LINKER_SCRIPT) $(OBJS) -o $@ $(LIBS)
	$(OBJDUMP) -dh  $@ >$@.headers
	@echo   $(CURDIR)/$@.headers
