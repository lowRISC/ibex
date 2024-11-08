ROOT_DIR            :=  $(shell git rev-parse --show-toplevel)
mkfile_path         := $(shell git rev-parse --show-toplevel)/isolde/lca_system
IBEX_CONFIG         ?=  isolde
FUSESOC_CONFIG_OPTS := $(shell cd $(ROOT_DIR) && $(ROOT_DIR)/util/ibex_config.py $(IBEX_CONFIG) fusesoc_opts)
FUSESOC_PARAMS      ?=
TEST                ?= vlinstr_test
TEST_SRC_DIR	    = $(ROOT_DIR)/isolde/sw/simple_system/$(TEST)
TEST_BIN_DIR	    = $(mkfile_path)/sw/bin
test-program        ?= $(TEST_BIN_DIR)/$(TEST)
BUILD_DIR           := build/$(IBEX_CONFIG)
SYNTH_DIR           := synth/$(IBEX_CONFIG)
TMP_DIR             := tmp/$(IBEX_CONFIG)
FUSESOC_BUILD_ROOT  :=$(mkfile_path)/$(TMP_DIR)
FUSESOC_PROJECT     := isolde
FUSESOC_CORE        := ibex
FUSESOC_SYSTEM      := lca_system
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


include Makefile.verilator




.PHONY: sim-inputs
sim-inputs:
	$(MAKE)  TEST=redmule TEST_FILES=redmule.c TEST_SRC_DIR=$(REDMULE_ROOT_DIR)/sw test-app


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

	

.PHONY: test-app $(test-program) clean $(TEST_BIN_DIR)

$(TEST_BIN_DIR):
	mkdir -p $@


$(test-program).hex: $(test-program).elf
test-app: $(TEST_BIN_DIR) $(test-program).hex

clean-test:
	rm -f $(test-program)*



clean: veri-clean clean-test-programs
	rm -fr $(BUILD_DIR) $(TEST_BIN_DIR) logs 
	rm -f *.log *.csv

clean-hw:
	rm -fr $(BUILD_DIR) logs

