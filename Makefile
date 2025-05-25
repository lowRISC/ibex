IBEX_CONFIG ?= small

FUSESOC_CONFIG_OPTS = $(shell ./util/ibex_config.py $(IBEX_CONFIG) fusesoc_opts)

all: help

.PHONY: help
help:
	@echo "The following targets are a good starting point for newcomers:"
	@echo ""
	@echo " > Run ibex simulations using verilator"
	@echo " make run-simple-system-hello"
	@echo " make run-coremark"
	@echo " make run-pmp-smoke-test"
	@echo " make run-csr-test"
	@echo ""
	@echo " > Run ibex DV environment"
	@echo " > (If you have access to EDA simulation tools)"
	@echo " make -C dv/uvm/core_ibex SIMULATOR=xlm ITERATIONS=4 TEST=riscv_rand_instr_test COV=1"
	@echo ""
	@echo " > Run yosys flow using nangate45"
	@echo " make run_syn_yosys_nangate45"
	@echo ""
	@echo " > (caution: clears all working changes)"
	@echo " make reset"

# Use a parallel run (make -j N) for a faster build
build-all: build-riscv-compliance build-simple-system build-arty-100 \
      build-csr-test


#################
# Simple system #
#################

# Use the following targets:
.PHONY: build-simple-system
.PHONY: build-simple-system-hello-bin
.PHONY: run-simple-system-hello

simple-system-Vibex=build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system
hello-bin=examples/sw/simple_system/hello_test/hello_test.vmem

build-simple-system: $(simple-system-Vibex)
$(simple-system-Vibex):
	fusesoc --cores-root=. run --target=sim --setup --build \
		lowrisc:ibex:ibex_simple_system \
		$(FUSESOC_CONFIG_OPTS)

build-simple-system-hello-bin: $(hello-bin)
$(hello-bin):
	cd examples/sw/simple_system/hello_test && $(MAKE)

run-simple-system-hello: $(hello-bin) $(simple-system-Vibex)
	build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system \
			--raminit=$(hello-bin)
	@echo ""
	cat ibex_simple_system.log

# Coremark
# See 'examples/sw/benchmarks/README.md' for more details

# Use the following targets:
.PHONY: build-ss-maxperf-coremark
.PHONY: build-coremark-sw
.PHONY: run-coremark

coremark-maxperf-Vibex=build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system
coremark-bin=examples/sw/benchmarks/coremark/coremark.elf

build-ss-maxperf-coremark: $(coremark-maxperf-Vibex)
$(coremark-maxperf-Vibex):
	fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ibex:ibex_simple_system `./util/ibex_config.py maxperf fusesoc_opts`

build-coremark-sw: $(coremark-bin)
$(coremark-bin):
	make -C ./examples/sw/benchmarks/coremark/

run-coremark: build-ss-maxperf-coremark build-coremark-sw
	$(coremark-maxperf-Vibex) --meminit=ram,$(coremark-bin)
	@echo ""
	grep "CoreMark" ./ibex_simple_system.log

# pmp_smoke_test

# Use the following targets:
.PHONY: build-simple-system
.PHONY: build-pmp-smoke-test-sw
.PHONY: run-pmp-smoke-test

pmp-smoke-test-bin=examples/sw/simple_system/pmp_smoke_test/pmp_smoke_test.elf

build-pmp-smoke-test-sw: $(pmp-smoke-test-bin)
$(pmp-smoke-test-bin):
	make -C ./examples/sw/simple_system/pmp_smoke_test

run-pmp-smoke-test: build-simple-system build-pmp-smoke-test-sw
	$(simple-system-Vibex) --meminit=ram,$(pmp-smoke-test-bin)
	@echo ""
	cat ibex_simple_system.log

########################
# Arty A7 FPGA example #
########################

# DEAD - DO NOT USE THIS SECTION #

# Use the following targets (depending on your hardware):
.PHONY: build-arty-35
.PHONY: build-arty-100
.PHONY: program-arty

arty-sw-program = examples/sw/led/led.vmem
sw-led: $(arty-sw-program)

.PHONY: $(arty-sw-program)
$(arty-sw-program):
	cd examples/sw/led && $(MAKE)

build-arty-35: sw-led
	fusesoc --cores-root=. run --target=synth --setup --build \
		lowrisc:ibex:top_artya7 --part xc7a35ticsg324-1L

build-arty-100: sw-led
	fusesoc --cores-root=. run --target=synth --setup --build \
		lowrisc:ibex:top_artya7 --part xc7a100tcsg324-1

program-arty:
	fusesoc --cores-root=. run --target=synth --run \
		lowrisc:ibex:top_artya7


##########################
# CS Registers testbench #
##########################

# Use the following targets:
.PHONY: build-csr-test
.PHONY: run-csr-test

build-csr-test:
	fusesoc --cores-root=. run --target=sim --setup --build \
	      --tool=verilator lowrisc:ibex:tb_cs_registers
Vtb_cs_registers = \
      build/lowrisc_ibex_tb_cs_registers_0/sim-verilator/Vtb_cs_registers
$(Vtb_cs_registers):
	@echo "$@ not found"
	@echo "Run \"make build-csr-test\" to create the dependency"
	@false

run-csr-test: | $(Vtb_cs_registers)
	fusesoc --cores-root=. run --target=sim --run \
	      --tool=verilator lowrisc:ibex:tb_cs_registers

#############
# Synthesis #
#############

# Use the following targets:
.PHONY: run_syn_yosys_nangate45

run_syn_yosys_nangate45:
	pushd syn/ && \
	./syn_yosys.sh && \
	popd

#########
# Other #
#########

# RISC-V compliance
.PHONY: build-riscv-compliance
build-riscv-compliance:
	fusesoc --cores-root=. run --target=sim --setup --build \
		lowrisc:ibex:ibex_riscv_compliance \
		$(FUSESOC_CONFIG_OPTS)


########
# UTIL #
########

# Lint check
.PHONY: lint-top-tracing
lint-top-tracing:
	fusesoc --cores-root . run --target=lint lowrisc:ibex:ibex_top_tracing \
		$(FUSESOC_CONFIG_OPTS)

# Echo the parameters passed to fusesoc for the chosen IBEX_CONFIG
.PHONY: test-cfg
test-cfg:
	@echo $(FUSESOC_CONFIG_OPTS)

.PHONY: python-lint
python-lint:
	$(MAKE) -C util lint

.PHONY: clean
clean:
	rm -rf build/

.PHONY: reset
reset:
	git clean -ffdx; git clean -ffdX; git reset --hard HEAD

