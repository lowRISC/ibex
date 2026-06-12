# Snippy CMake flow for Ibex DV

You can download the llvm-snippy here: [llvm-snippy](https://github.com/LLVM-Snippy/llvm-snippy)

This directory contains the CMake implementation of the custom llvm-snippy flow
for Ibex DV.

The usual entry point is the Ibex Makefile target described in `../README.md`:

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

This README focuses on the CMake flow itself: Snippy input files, standalone
CMake usage, coverage exclude files, and toolchain notes.

## Snippy input files

The Snippy-specific input files are stored under:

```text
dv/uvm/core_ibex/snippy/
```

The important subdirectories are:

```text
snippy/yaml_tests/
snippy/asm_func/
snippy/linker/
snippy/urg_exclude/
```

### `snippy/yaml_tests`

This directory contains llvm-snippy YAML test scenarios.

The existing YAML files are intended to exercise instruction and layout
scenarios needed for functional coverage closure. New Snippy scenarios can be
added here and run in the same way as the existing layouts.

Only YAML files whose names start with `layout_` are treated as runnable Snippy
test scenarios by the default flow. Other YAML files in this directory are
section descriptions or helper inputs.

For example, a file:

```text
snippy/yaml_tests/layout_arith.yaml
```

can be selected with any of these forms:

```text
layout_arith
arith
layout_arith.yaml
```

Example:

```bash
make run_snippy \
  OUT=out \
  COV=1 \
  SIMULATOR=vcs \
  IBEX_CONFIG=opentitan \
  RV32ZC=ibex_pkg::RV32Zca \
  SNIPPY_ITERATIONS=3 \
  SNIPPY_TEST="layout_arith"
```

Multiple layouts can be selected with a comma-separated list (escape sequences are ignored):

```bash
SNIPPY_TEST="layout_arith, jalr, rem_div"
```

### Selecting the Snippy YAML directory

By default, Snippy YAML layouts are read from:

```text
snippy/yaml_tests
```

`SNIPPY_TEST` selects YAML files from this directory. The directory can be
overridden from the Makefile bridge with `SNIPPY_YAML_DIR`:

```bash
make run_snippy \
  OUT=out \
  SNIPPY_YAML_DIR=snippy/zcmp_yaml_tests \
  SNIPPY_TEST="layout_zcmp_push_pop"
```

`SNIPPY_YAML_DIR` may be either an absolute path or a path relative to:

```text
dv/uvm/core_ibex
```

The same directory can also be overridden when configuring CMake directly with
`YAML_DIR`:

```bash
cmake -B out/snippy_cmake_build \
  -DOUT="$(pwd)/out" \
  -DYAML_DIR=snippy/zcmp_yaml_tests \
  -DSNIPPY_TEST="layout_zcmp_push_pop"
```

Absolute paths are also accepted:

```bash
cmake -B out/snippy_cmake_build \
  -DOUT="$(pwd)/out" \
  -DYAML_DIR=/path/to/snippy/yaml_tests \
  -DSNIPPY_TEST="layout_zcmp_push_pop"
```

### `snippy/asm_func`

This directory contains assembly helper code that can be called from Snippy
tests.

The current implementation provides a helper function that executes illegal
instructions. Snippy calls this function from the `layout_illegal` test.

Additional assembly helper functions can be implemented in this directory if a
test needs behavior that is easier to express in hand-written assembly. Such
functions can then be called from Snippy YAML tests in the same way as the
existing illegal-instruction helper.

### `snippy/linker`

This directory contains the base linker script template.

For every Snippy run, CMake generates a per-run linker script from this template.
Generated linker scripts are placed under the CMake build tree, for example:

```text
out/snippy_cmake_build/tests/layout_arith/layout_arith_0/linker/linker.ld
```

### `snippy/urg_exclude`

This directory contains coverage exclude files used by the VCS/URG coverage
merge flow.

These excludes are needed because llvm-snippy is an LLVM-based generator. It is
intended to generate user-level instruction streams and is not a replacement for
the existing privileged-mode ISA tests. As a result, privileged ISA coverage
points that are not targeted by Snippy are excluded from the Snippy coverage
merge. Since llvm-snippy follows the ISA extension state supported by LLVM, the
exclude files also waive coverage points for instructions that are not generated
from the current LLVM view of the enabled extensions, for example instructions
from older versions of the bitmanip extension.

The default exclude file is:

```text
snippy/urg_exclude/urg_exclude_all.txt
```

When enabled, CMake forwards this file to the Ibex coverage flow as
`VCS_URG_ELFILE`, and the VCS coverage merge uses it as an URG exclude/waiver
file.

The option is controlled by:

```text
USE_URG_EXCLUDE
```

Default behavior:

```text
USE_URG_EXCLUDE=ON
```

To disable the exclude file through the Makefile bridge:

```bash
make run_snippy \
  OUT=out \
  COV=1 \
  USE_URG_EXCLUDE=OFF \
  SIMULATOR=vcs \
  IBEX_CONFIG=opentitan \
  RV32ZC=ibex_pkg::RV32Zca \
  SNIPPY_ITERATIONS=3 \
  SNIPPY_TEST="layout_arith"
```

Then run coverage as usual:

```bash
make coverage_snippy OUT=out
```

For direct CMake usage, pass:

```bash
-DUSE_URG_EXCLUDE=OFF
```

The value is stored in the CMake cache under `out/snippy_cmake_build`, so change
it at configure time, before running the coverage target.

## What the flow does

For each selected Snippy YAML layout and each requested run, the flow:

1. runs `llvm-snippy` and produces a relocatable Snippy ELF;
2. generates a per-run linker script;
3. links the Snippy ELF with the riscv-dv bootstrap assembly;
4. generates an ELF layout `.svload` file;
5. runs the Ibex RTL simulation through the standard Ibex simulator flow;
6. writes standard Ibex-compatible runtime artifacts under `OUT/run/tests`;
7. updates a CMake-side Snippy JSON summary.

Runtime artifacts are written to:

```text
OUT/run/tests/snippy_<layout>.<seed>/
```

CMake-side intermediate files are written to:

```text
OUT/snippy_cmake_build/
```

The aggregate Snippy summary is written to:

```text
OUT/snippy_cmake_build/summary/snippy_summary.json
```

## Running through the Ibex Makefile

The normal way to run Snippy tests is through the Ibex Makefile target
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
  SNIPPY_TEST="layout_arith, jalr, rem_div"
```

Combined riscv-dv and Snippy coverage is described in `../README.md`.

## Running directly with CMake

The Snippy flow can also be run directly with CMake. This is useful when
debugging the Snippy flow itself, because it avoids the outer Ibex Makefile
bridge.

Run from:

```text
dv/uvm/core_ibex
```

Configure:

```bash
cmake -B out/snippy_cmake_build \
  -DOUT="$(pwd)/out" \
  -DCOV=1 \
  -DFUNCTIONAL_COV=0 \
  -DSIMULATOR=vcs \
  -DIBEX_CONFIG=opentitan \
  -DRV32ZC=ibex_pkg::RV32Zca \
  -DSNIPPY_ITERATIONS=3 \
  -DSNIPPY_TEST="layout_arith, jalr, rem_div"
```

Build and run:

```bash
cmake --build out/snippy_cmake_build --target run_all -j60
```

Coverage can then be merged with:

```bash
cmake --build out/snippy_cmake_build --target coverage
```

To disable the URG exclude file in direct CMake mode, configure with:

```bash
-DUSE_URG_EXCLUDE=OFF
```

## Running directly with Ninja

Ninja can be used as the CMake generator:

```bash
cmake -G Ninja -B out/snippy_cmake_build \
  -DOUT="$(pwd)/out" \
  -DCOV=1 \
  -DFUNCTIONAL_COV=0 \
  -DSIMULATOR=vcs \
  -DIBEX_CONFIG=opentitan \
  -DRV32ZC=ibex_pkg::RV32Zca \
  -DSNIPPY_ITERATIONS=3 \
  -DSNIPPY_TEST="layout_arith, jalr, rem_div"
```

Then run:

```bash
cmake --build out/snippy_cmake_build --target run_all
```

With Ninja, parallel scheduling is handled by Ninja itself, so it is usually not
necessary to pass a manual `-j` value.

Coverage:

```bash
cmake --build out/snippy_cmake_build --target coverage
```

## Important CMake options

```text
OUT
    Ibex output directory. Snippy runtime artifacts are written into this tree.

COV
    Enable RTL coverage collection.

FUNCTIONAL_COV
    Enable functional coverage collection.

SIMULATOR
    RTL simulator, for example vcs or xlm.

IBEX_CONFIG
    Ibex configuration name.

RV32ZC
    Optional compressed-extension subset override.

SNIPPY_TEST
    Comma-separated list of Snippy YAML layouts.

SNIPPY_ITERATIONS
    Number of Snippy runs for each selected layout.

SNIPPY_GCC_MARCH
    RISC-V -march value used during the Snippy link step.

SNIPPY_GCC_MABI
    RISC-V -mabi value used during the Snippy link step.

SNIPPY_RTL_TEST
    UVM test used for ELF-layout simulation.

SNIPPY_TIMEOUT_S
    RTL simulation timeout.

USE_URG_EXCLUDE
    Use snippy/urg_exclude/urg_exclude_all.txt during VCS/URG coverage merge.
```

## Toolchain notes

The Snippy flow uses the same toolchain environment variables as the standard
Ibex Makefile flow:

```bash
export RISCV_GCC=/path/to/riscv32-unknown-elf-gcc
export RISCV_OBJCOPY=/path/to/riscv32-unknown-elf-objcopy
export SPIKE_PATH=/path/to/spike/bin
export PKG_CONFIG_PATH=/path/to/spike/lib/pkgconfig
```

The llvm-snippy installation is selected with:

```bash
export SC_SNIPPY_PATH=/path/to/llvm-snippy
```

The expected executable is:

```text
$SC_SNIPPY_PATH/llvm-snippy
```

Use [llvm-snippy3.0](https://github.com/LLVM-Snippy/llvm-snippy/releases/tag/snippy-3.0).

### GCC compatibility

The riscv-dv and Snippy flows can expose different GCC compatibility issues.

For riscv-dv tests using the B extension, the selected GCC must support the
requested ISA. Otherwise, an error like this can appear:

```text
riscv64-unknown-elf-gcc: error: '-march=rv32imcb': extension 'b' is unsupported standard single letter extension
```

For Snippy linking, some toolchains may reject RISC-V architecture strings or
ELF attributes produced by other tools. One observed error is:

```text
Assembler messages:
Fatal error: -march=rv32imc_zicsr_zba_zbb_zbc_zbs: z ISA extension not in alphabetical order: 'zba' must come before 'zicsr'.
```

The Snippy CMake command line uses the ordered default:

```text
SNIPPY_GCC_MARCH=rv32imc_zba_zbb_zbc_zbs_zicsr
```

When the assembler still reports the old order, the problem is likely a
toolchain compatibility issue rather than the CMake command line itself.

A possible source for compatible prebuilt toolchains is:

```text
https://syntacore.com/tools/development-tools
```

## Cleaning

For the integrated Makefile flow, prefer:

```bash
make clean OUT=out
```

This removes:

```text
out/
riscv_dv_extension/riscv_core_setting.sv
```


For direct CMake debugging, the CMake build tree can also be removed manually:

```bash
rm -rf out/snippy_cmake_build
```
