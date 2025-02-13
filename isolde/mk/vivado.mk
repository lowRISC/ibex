###############################################################################
#
# Copyleft  2024 ISOLDE
#
###############################################################################


synth-setup:
	mkdir -p $(SYNTH_DIR)
	fusesoc --cores-root=$(ROOT_DIR) run --target=synth --setup  --no-export --build-root=$(SYNTH_DIR) isolde:ibex:ibex_simple_system $(FUSESOC_CONFIG_OPTS)

.PHONY: synth
synth: synth-setup
	cd ./synth/isolde/synth-vivado && \
	echo "launch_runs synth_1 " >launch_runs.tcl && \
	echo "wait_on_runs synth_1" >>launch_runs.tcl && \
	vivado -mode batch -source ./isolde_ibex_ibex_simple_system_0.tcl ./launch_runs.tcl | tee vivado.log

	
