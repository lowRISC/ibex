ROOT_DIR            :=  $(shell git rev-parse --show-toplevel)
IBEX_CONFIG         ?=  small
FUSESOC_CONFIG_OPTS := $(shell cd $(ROOT_DIR) && $(ROOT_DIR)/util/ibex_config.py $(IBEX_CONFIG) fusesoc_opts)
test-program        ?= $(ROOT_DIR)/examples/sw/simple_system/hello_test/hello_test.elf

num_cores := $(shell nproc)
num_cores_half := $(shell echo "$$(($(num_cores) / 2))")

build-hw:
	fusesoc --cores-root=$(ROOT_DIR) run --target=sim --setup --build  isolde:ibex:ibex_simple_system $(FUSESOC_CONFIG_OPTS)



.PHONY: test-program $(test-program) clean
# Rule for test-program
$(test-program):
	make -C $(dir $@)

test-program: $(test-program)


run-test:
	./build/isolde_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system -t --meminit=ram,$(test-program)

clean:
	rm -f $(test-program)
	rm -fr build logs
	rm -f *.log *.csv
	