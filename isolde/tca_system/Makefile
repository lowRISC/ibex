ROOT_DIR            :=  $(shell git rev-parse --show-toplevel)
mkfile_path         := $(shell git rev-parse --show-toplevel)/isolde/tca_system
IBEX_CONFIG         ?=  isolde
FUSESOC_CONFIG_OPTS := $(shell cd $(ROOT_DIR) && $(ROOT_DIR)/util/ibex_config.py $(IBEX_CONFIG) fusesoc_opts)
FUSESOC_PARAMS      ?=
TEST                ?= redmule_complex
TEST_SRC_DIR	    = $(ROOT_DIR)/isolde/sw/$(TEST)
TEST_BIN_DIR	    = $(mkfile_path)/sw/bin
test-program        ?= $(TEST_BIN_DIR)/$(TEST)
SYNTH_DIR           := synth/$(IBEX_CONFIG)
TMP_DIR             := tmp/$(IBEX_CONFIG)
FUSESOC_BUILD_ROOT  :=$(mkfile_path)/$(TMP_DIR)
FUSESOC_PROJECT     := isolde
FUSESOC_CORE        := ibex
FUSESOC_SYSTEM      := tca_system
FUSESOC_PKG_NAME    := $(FUSESOC_PROJECT):$(FUSESOC_CORE):$(FUSESOC_SYSTEM)
## redmule config
REDMULE_ROOT_DIR :=$(shell bender path redmule)
##
#
CV_SIMULATOR         :=  verilator
CV_SW_TOOLCHAIN      :=  $(shell git rev-parse --show-toplevel)/install/riscv-gcc
CV_SW_PREFIX         :=  riscv32-unknown-elf-
CV_SW_MARCH          :=  rv32im_zicsr
CV_SW_CC             :=  gcc 



num_cores := $(shell nproc)
num_cores_half := $(shell echo "$$(($(num_cores) / 2))")

REDMULE_COMPLEX := 1
export REDMULE_COMPLEX
###
VLT_TOP_MODULE      ?= tb_tca_system
IMEM_LATENCY        ?= 0
VLT_TOP_MODULE_PARAMS := -GIMEM_LATENCY=$(IMEM_LATENCY)



include ../mk/sw-build.mk
include ../mk/verilator-build.mk



.PHONY: sim-input
sim-input:
	$(MAKE)  TEST=redmule_complex TEST_FILES=redmule_complex.c TEST_SRC_DIR=$(REDMULE_ROOT_DIR)/sw test-build


$(SIM_TEST_INPUTS):
	mkdir -p $(SIM_TEST_INPUTS)	

$(SIM_TEST_INPUTS)/$(TEST).hex: $(SIM_TEST_INPUTS)/$(TEST).elf


golden:
	make -C $(REDMULE_ROOT_DIR) $@
	

synth-setup:
	mkdir -p $(SYNTH_DIR)
	fusesoc --cores-root=$(ROOT_DIR) run --target=synth --setup  --no-export --build-root=$(SYNTH_DIR) isolde:ibex:ibex_simple_system $(FUSESOC_CONFIG_OPTS)

.PHONY: synth
synth: synth-setup
	cd ./synth/isolde/synth-vivado && \
	echo "launch_runs synth_1 " >launch_runs.tcl && \
	echo "wait_on_runs synth_1" >>launch_runs.tcl && \
	vivado -mode batch -source ./isolde_ibex_ibex_simple_system_0.tcl ./launch_runs.tcl | tee vivado.log

	

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

