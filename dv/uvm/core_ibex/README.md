# DV for the ibex core

For detailed documention on how Ibex's verification works, please have a look at [the dedicated documentation page](https://ibex-core.readthedocs.io/en/latest/03_reference/verification.html).
This README provides a quick start guide to get things running.

## Prerequisites
You need to have Xcelium available on your machine.
You can check whether you have it available by running: `xrun --verison`

You also need Spike to be able to compare to in the cosimulation.
We use a lowRISC specific Spike which you can find [on its own GitHub page](https://github.com/lowRISC/riscv-isa-sim/tree/ibex_cosim).
Some quick build instructions from within the `riscv-isa-sim` repo:
```bash
mkdir build
cd build
../configure --enable-commitlog --enable-misaligned --prefix=$SPIKE_INSTALL_DIR
make
make install
export SPIKE_PATH=$SPIKE_INSTALL_DIR/bin
export PKG_CONFIG_PATH=$PKG_CONFIG_PATH:$SPIKE_INSTALL_DIR/lib/pkgconfig
```

You will need the [RISC-V toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain).
You'll need to add this to your path and then also set the following environment variables:
```bash
export RISCV_GCC=riscv32-unknown-elf-gcc
export RISCV_OBJCOPY=riscv32-unknown-elf-objcopy
```

For the optional llvm-snippy flow, set `SC_SNIPPY_PATH` to the llvm-snippy
installation directory:

```bash
export SC_SNIPPY_PATH=/path/to/llvm-snippy
```

The Snippy flow expects the executable at `$SC_SNIPPY_PATH/llvm-snippy`.
More Snippy-specific setup notes are documented in `snippy_cmake/README.md`.

## Running tests

To run tests you can make variations of the following command, where you replace `$TEST_NAME` with the test (or a series of comma-separated tests) that you would like to run as specified in `dv/uvm/core_ibex/riscv_dv_extension/testlist.yaml`:
```bash
make --keep-going IBEX_CONFIG=opentitan SIMULATOR=xlm ISS=spike ITERATIONS=1 SEED=1 TEST=$TEST_NAME WAVES=0 COV=0
```

## Running Snippy tests

The custom Snippy flow can be launched through the Ibex Makefile with
`run_snippy`.

Example:

```bash
make run_snippy \
  OUT=out \
  COV=1 \
  SIMULATOR=vcs \
  IBEX_CONFIG=opentitan \
  RV32ZC=ibex_pkg::RV32Zca \
  SNIPPY_ITERATIONS=3 \
  SNIPPY_TEST="layout_arith, jalr, rem_div" \
  SNIPPY_YAML_DIR=snippy/yaml_tests
```

`SNIPPY_TEST` selects YAML files from `SNIPPY_YAML_DIR`.

`SNIPPY_TEST` is a comma-separated list of Snippy YAML layouts. The accepted
forms include `layout_arith`, `arith`, and `layout_arith.yaml`.

`SNIPPY_ITERATIONS` controls the number of Snippy runs for each selected layout.

Snippy runtime results are written into the standard Ibex output tree:

```text
out/run/tests/snippy_<layout>.<seed>/
```

The CMake-side Snippy intermediate files and summary are written under:

```text
out/snippy_cmake_build/
```

## Collecting combined riscv-dv and Snippy coverage

To collect one combined coverage report from both riscv-dv and Snippy runs, use
the same `OUT` directory and enable `COV=1` for both flows.

First, run riscv-dv only up to RTL simulation:

```bash
make run \
  GOAL=rtl_sim_run \
  OUT=out \
  COV=1 \
  SIMULATOR=vcs \
  IBEX_CONFIG=opentitan \
  RV32ZC=ibex_pkg::RV32Zca \
  TEST=riscv_arithmetic_basic_test
```

Using `GOAL=rtl_sim_run` avoids collecting an intermediate coverage report
before the Snippy tests have been added.

Then run Snippy into the same `OUT` directory:

```bash
make run_snippy \
  OUT=out \
  COV=1 \
  SIMULATOR=vcs \
  IBEX_CONFIG=opentitan \
  RV32ZC=ibex_pkg::RV32Zca \
  SNIPPY_ITERATIONS=3 \
  SNIPPY_TEST="layout_arith, jalr, rem_div"
```

Finally, merge coverage once:

```bash
make coverage_snippy OUT=out
```

The final report is written to:

```text
out/run/coverage/report/
```

## Cleaning generated files

To remove generated outputs:

```bash
make clean OUT=out
```

This also removes the Snippy CMake build directory when it is located under
`OUT`, for example:

```text
out/snippy_cmake_build/
```