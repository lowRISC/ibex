ROOT_DIR            :=  $(shell git rev-parse --show-toplevel)
mkfile_path         := $(shell git rev-parse --show-toplevel)/isolde/lca_system
IBEX_CONFIG         ?=  isolde
FUSESOC_CONFIG_OPTS := $(shell cd $(ROOT_DIR) && $(ROOT_DIR)/util/ibex_config.py $(IBEX_CONFIG) fusesoc_opts)
FUSESOC_PARAMS      ?=
TEST                ?= dhrystone
TEST_SRC_DIR	    = $(ROOT_DIR)/isolde/sw/$(TEST)
TEST_BIN_DIR	    = $(mkfile_path)/sw/bin
test-program        ?= $(TEST_BIN_DIR)/$(TEST)
BUILD_DIR           := build/$(IBEX_CONFIG)
SYNTH_DIR           := synth/$(IBEX_CONFIG)
TMP_DIR             := tmp/$(IBEX_CONFIG)
FUSESOC_BUILD_ROOT  :=$(mkfile_path)/$(TMP_DIR)
FUSESOC_PROJECT     := isolde
FUSESOC_CORE        := ibex
FUSESOC_SYSTEM      := lca_dm_system
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





###
VLT_TOP_MODULE        ?= tb_lca_system
IMEM_LATENCY          ?= 0
VLT_TOP_MODULE_PARAMS := -GIMEM_LATENCY=$(IMEM_LATENCY)

###
# Static configurations (can be overridden by command-line)
###
DBG_MODULE   ?= 0
ENABLE_SPM   ?= 0


verilator_target := vanilla
# Select testbench target 
ifeq ($(DBG_MODULE),1)
    tb_target += -t tb_dm -t rv_debug
endif
ifeq ($(ENABLE_SPM),1)
    tb_target += -t spm
endif

tb_target ?= -t vanilla_lca


common_targs +=  $(tb_target)




include ../mk/redmule.mk
include ../mk/sw-build.mk
include ../mk/verilator-build.mk
include ../mk/vivado.mk



	


		