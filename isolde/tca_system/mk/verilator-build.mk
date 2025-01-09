###############################################################################
#
# Copyleft  2024 ISOLDE

#############
# Verilator #
#############

include $(REDMULE_ROOT_DIR)/bender_common.mk
include $(REDMULE_ROOT_DIR)/bender_sim.mk
include $(REDMULE_ROOT_DIR)/bender_synth.mk



VLT_TOP_MODULE ?= tb_tca_system

#####
VERI_LOG_DIR      ?= $(mkfile_path)/log/$(VLT_TOP_MODULE)/$(IMEM_LATENCY)
SIM_TEST_INPUTS   ?= $(mkfile_path)/vsim
BIN_DIR           = $(mkfile_path)/bin/$(VLT_TOP_MODULE)/$(IMEM_LATENCY)
VERI_FLAGS        +=



.PHONY: veri-clean 

# Clean all build directories and temporary files for Questasim simulation
veri-clean: 
	rm -f *.flist
	rm -fr log/$(VLT_TOP_MODULE) 
	make -C sim/core -f Makefile.verilator  	 SIM_RESULTS=$(BIN_DIR)                  \
												   RUN_INDEX=$(IMEM_LATENCY)           \
											  VLT_TOP_MODULE=$(VLT_TOP_MODULE)           \
									   VLT_TOP_MODULE_PARAMS=$(VLT_TOP_MODULE_PARAMS)    \
									 $@
	rm -fr $(FUSESOC_BUILD_ROOT) 

#verilate: $(BIN_DIR)/verilator_executable

##

CORE_FILES := $(filter %.core,$(wildcard $(mkfile_path)/*))
CORE_FILES += $(filter %.core,$(wildcard $(ROOT_DIR)/*))
CORE_FILE_NAMES := $(notdir $(CORE_FILES))

fusesoc_ignore: $(ROOT_DIR)/isolde/tca_system/.bender/FUSESOC_IGNORE $(ROOT_DIR)/vendor/redmule/FUSESOC_IGNORE

$(ROOT_DIR)/isolde/tca_system/.bender/FUSESOC_IGNORE:
	@if [ ! -f $@ ]; then touch $@; fi

$(ROOT_DIR)/vendor/redmule/FUSESOC_IGNORE:
	@if [ ! -f $@ ]; then touch $@; fi



ibex_sim.flist:  $(CORE_FILES)
	@echo $(CORE_FILE_NAMES)
	fusesoc --cores-root=$(ROOT_DIR) run --target=sim --setup --no-export $(FUSESOC_PARAMS)  --build-root=$(FUSESOC_BUILD_ROOT) $(FUSESOC_PKG_NAME) $(FUSESOC_CONFIG_OPTS) 
	python $(ROOT_DIR)/util/transform_paths.py  \
										       $(FUSESOC_BUILD_ROOT)/sim-verilator  \
	                                           $(FUSESOC_BUILD_ROOT)/sim-verilator/$(FUSESOC_PROJECT)_$(FUSESOC_CORE)_$(FUSESOC_SYSTEM)_0.vc \
											   $@
	touch $@
##

manifest.flist: Bender.yml
	@echo 'INFO:  bender script verilator $(common_targs) $(VLT_BENDER)'
	@$(BENDER) script verilator $(common_targs) $(VLT_BENDER)  >$@
	touch $@

#$(BIN_DIR)/verilator_executable:  ibex_sim.flist manifest.flist
verilate:  ibex_sim.flist manifest.flist
#	mkdir -p $(dir $@)
	mkdir -p $(BIN_DIR)
	make -C sim/core -f Makefile.verilator CV_CORE_MANIFEST=${CURDIR}/ibex_sim.flist     \
											     PE_MANIFEST=${CURDIR}/manifest.flist    \
	                                             SIM_RESULTS=$(BIN_DIR)                  \
												   RUN_INDEX=$(IMEM_LATENCY)           \
											  VLT_TOP_MODULE=$(VLT_TOP_MODULE)           \
									   VLT_TOP_MODULE_PARAMS=$(VLT_TOP_MODULE_PARAMS)    \
											  verilate      



.PHONY: veri-run
veri-run: $(BIN_DIR)/verilator_executable 
	@echo "$(BANNER)"
	@echo "* Running with Verilator: "
	@echo "*                            logfile: $(VERI_LOG_DIR)/$(TEST).log"
	@echo "*                    rtl debug trace: $(VERI_LOG_DIR)/rtl_debug_trace.log"
	@echo "*                              *.vcd: $(VERI_LOG_DIR)"
	@echo "$(BANNER)"
	mkdir -p $(VERI_LOG_DIR)
	rm -f $(VERI_LOG_DIR)/verilator_tb.vcd
	$(BIN_DIR)/verilator_executable  \
		$(VERI_FLAGS) \
		"+STIM_INSTR=$(test-program)-m.hex" \
		"+STIM_DATA=$(test-program)-d.hex" \
		| tee $(VERI_LOG_DIR)/$(TEST).log
	mv verilator_tb.vcd $(VERI_LOG_DIR)/$(TEST).vcd
	mv rtl_debug_trace.log $(VERI_LOG_DIR)


.PHONY: help
help:
	@echo "verilator related available targets:"
	@echo verilate                                 -- builds verilator simulation, available here: $(BIN_DIR)/verilator_executable
	@echo veri-run                                 -- runs the test
	@echo veri-clean                               -- gets a clean slate for simulation
	@echo verilate VLT_TOP_MODULE=tb_top_verilator
	
