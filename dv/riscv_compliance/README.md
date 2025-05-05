Ibex simulation for RISC-V Compliance Testing
=============================================

This directory contains a compiled simulation of Ibex to be used as target
in the [RISC-V Compliance Test](https://github.com/riscv/riscv-compliance).
In addition to Ibex itself, it contains a 64 kB RAM and a memory-mapped helper
module to interact with the software, e.g. to dump out the test signature and to
end the simulation.

The simulation is designed for Verilator, but can be adapted to other simulators
if needed.

How to run RISC-V Compliance on Ibex
------------------------------------

0. Check your prerequisites
   To compile the simulation and run the compliance test suite you need to
   have the following tools installed:
   - Verilator
   - fusesoc
   - srecord (for `srec_cat`)
   - RISC-V Compiler toolchain (RV64)
   - RISC-V SAIL Model

   On Ubuntu/Debian, install the required tools like this:

   ```sh
   sudo apt-get install -y srecord python3-pip gcc-riscv64-unknown-elf
   pip3 install --user -U fusesoc
   pip3 install -U riscof
   ```

   We recommend installing Verilator from source as versions from Linux
   distributions are often outdated. Follow [this](https://www.veripool.org/projects/verilator/wiki/Installing) link for installation instructions. Pre-build SAIL RISCV model is available in [bin](/dv/riscv_compliance/bin/) directory, along with the instructions.

:warning: Run the following commands from base of the Ibex repo.

1. Get the RISC-V Architecture Compatibility test

   ```
   git clone https://github.com/riscv-non-isa/riscv-arch-test
   ```

2. Run the test suite

   The following commnad will run all tests of `rv32i_m` for supported ISA extensions of ibex. To run the tests for specific extensio (`I`, `M`, `C`, `Zifencei`, `privilege`), provide the path of respective extension test directory to the `--suite` flag.

   ```sh
   riscof run --config=config.ini \
   --suite=riscv-arch-test/riscv-test-suite/rv32i_m/ \
   --env=riscv-arch-test/riscv-test-suite/env
   ```

Compliance test suite system
----------------------------

This directory contains a system designed especially to run the compliance test
suite. The system consists of

- an Ibex core,
- a bus,
- a single-port memory for data and instructions,
- a bus-attached test utility.

The CPU core boots from SRAM at address 0x80000080.

The test utility is used by the software to end the simulation, and to inform
the simulator of the memory region where the test signature is stored.
The bus host reads the test signature from memory.

The memory map of the whole system is as follows:

| Start      | End        | Size   | Device                         |
|------------|------------|--------|--------------------------------|
| 0x80000000 | 0x801FFFFF | 2 MB   | shared instruction/data memory |
| 0x82000000 | 0x820003FF | 1 kB   | test utility                   |


The test utility provides the following registers relative to the base address.

| Address | R/W | Description                                                         |
|---------|-----|---------------------------------------------------------------------|
| 0x0     | W   | Write any value to dump the test signature and terminate simulation |
| 0x4     | W   | Start address of the test signature                                 |
| 0x8     | W   | End address of the test signature                                   |
