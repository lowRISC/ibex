ROOT_DIR            :=  $(shell git rev-parse --show-toplevel)
IBEX_CONFIG         ?=  isolde
FUSESOC_CONFIG_OPTS := $(shell cd $(ROOT_DIR) && $(ROOT_DIR)/util/ibex_config.py $(IBEX_CONFIG) fusesoc_opts)
test-program        := $(ROOT_DIR)/isolde/sw/simple_system/hello_test/hello_test.elf
BUILD_DIR           := build/$(IBEX_CONFIG)

num_cores := $(shell nproc)
num_cores_half := $(shell echo "$$(($(num_cores) / 2))")

build-hw:
	fusesoc --cores-root=$(ROOT_DIR) run --target=sim --setup --build  --build-root=$(BUILD_DIR) isolde:ibex:ibex_simple_system $(FUSESOC_CONFIG_OPTS)



.PHONY: test-program $(test-program) clean
# Rule for test-program
$(test-program):
	make -C $(dir $@)

test-app: $(test-program)

clean-test:
	make -C $(dir $(test-program)) clean

run-test:
	./$(BUILD_DIR)/sim-verilator/Vibex_simple_system -t --meminit=ram,$(test-program)
	@echo
	@echo ibex_simple_system.log
	@echo ======================
	@cat ibex_simple_system.log

clean:
#	rm -f $(test-program)
	make -C $(dir $(test-program)) clean
	rm -fr $(BUILD_DIR) logs
	rm -f *.log *.csv

clean-hw:
	rm -fr $(BUILD_DIR) logs

view-log:
	gtkwave  $(ROOT_DIR)/isolde/simple_system/logs/ibex.vcd --script=$(ROOT_DIR)/isolde/simple_system/load_waveform.tcl