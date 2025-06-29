ROOT_DIR            :=  $(shell git rev-parse --show-toplevel)
mkfile_path         :=  $(ROOT_DIR)/vendor/isolde-soc

VLT_TOP_MODULE        ?= tb_isolde_addr_shim
IMEM_LATENCY          := 0
common_targs += -t u_test


.PHONY: ibex_sim.flist


include $(ROOT_DIR)/isolde/mk/verilator-build.mk

ibex_sim.flist:  
	@echo "Unit test sim files"
	echo "$(mkfile_path)/tb/verilator/tb_top_verilator.cpp" >  ${CURDIR}/ibex_sim.flist
	echo "--top-module $(VLT_TOP_MODULE)"   >> ${CURDIR}/ibex_sim.flist