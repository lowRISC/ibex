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

##

ifeq ($(COMPILER), gcc)
	CV_SW_TOOLCHAIN      :=  $(shell git rev-parse --show-toplevel)/install/riscv-gcc
	CV_SW_PREFIX         :=  riscv32-unknown-elf-
	CV_SW_MARCH          :=  rv32im_zicsr
	CV_SW_CC_SUFFIX      :=  gcc 

else

	CV_SW_TOOLCHAIN      :=  $(shell git rev-parse --show-toplevel)/install/riscv-llvm
	CV_SW_PREFIX         :=  
	CV_SW_MARCH          :=  rv32im_zicsr
	CV_SW_CC_SUFFIX      :=  clang
endif





REDMULE_COMPLEX := 1
export REDMULE_COMPLEX
###
VLT_TOP_MODULE      ?= tb_tca_system
IMEM_LATENCY        ?= 0
VLT_TOP_MODULE_PARAMS := -GIMEM_LATENCY=$(IMEM_LATENCY)



include ../mk/sw-build.mk
include ../mk/verilator-build.mk
include ../mk/vivado.mk



	


		