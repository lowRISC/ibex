# Top-level user-configurable options for the Snippy flow.
#
# This file defines:
#   - source/tool locations,
#   - Ibex Make-compatible build options,
#   - Snippy-specific flow defaults,
#   - simple validation for user-provided values.

# CMAKE_CURRENT_SOURCE_DIR is expected to be:
#   ibex/dv/uvm/core_ibex
set(CORE_IBEX_ROOT "${CMAKE_CURRENT_SOURCE_DIR}")
get_filename_component(IBEX_ROOT "${CORE_IBEX_ROOT}/../../.." ABSOLUTE)

# Toolchain and Spike settings.
#
# These names intentionally match the normal Ibex Makefile environment. The
# Snippy CMake flow consumes the same variables instead of inventing a separate
# Snippy-specific toolchain configuration.
set(RISCV_GCC "$ENV{RISCV_GCC}" CACHE FILEPATH
    "RISC-V GCC executable used by the Ibex/Snippy flow")

set(RISCV_OBJCOPY "$ENV{RISCV_OBJCOPY}" CACHE FILEPATH
    "RISC-V objcopy executable used by the Ibex flow")

set(SPIKE_PATH "$ENV{SPIKE_PATH}" CACHE PATH
    "Spike bin directory used by the Ibex cosim flow")

set(PKG_CONFIG_PATH "$ENV{PKG_CONFIG_PATH}" CACHE STRING
    "pkg-config search path used to find Spike")

set(SNIPPY_ROOT "$ENV{SC_SNIPPY_PATH}" CACHE PATH
    "Path to the llvm-snippy installation root")

# Ibex Make-compatible knobs.
# Keep these names aligned with dv/uvm/core_ibex/Makefile so that the Snippy
# CMake flow can be called directly from the Ibex Makefile bridge.
set(OUT "${CMAKE_BINARY_DIR}/ibex_make_out" CACHE PATH
    "Output directory passed as OUT=... to the Ibex DV Makefile")

set(SEED "" CACHE STRING
    "Fixed seed for Ibex Make metadata and Snippy RTL runs. Empty means: use SNIPPY_COV_SEED for COV=ON and run index for COV=OFF")

set(WAVES "0" CACHE STRING
    "Enable waveform support in the Ibex DV Makefile compile flow")

set(COV OFF CACHE BOOL
    "Enable coverage collection")

set(SIMULATOR "vcs" CACHE STRING
    "RTL simulator used by the Ibex DV Makefile: vcs, xlm, questa, dsim, riviera, qrun")

set(ISS "spike" CACHE STRING
    "ISS used by the Ibex DV Makefile")

set(TEST "snippy_func_test" CACHE STRING
    "Placeholder Ibex test name used for metadata creation")

set(SIGNATURE_ADDR "8ffffffc" CACHE STRING
    "Pass/fail signature address used by the Ibex/riscv-dv flow")

set(IBEX_CONFIG "opentitan" CACHE STRING
    "Named Ibex configuration from ibex_configs.yaml")

set(RV32ZC "ibex_pkg::RV32ZcaZcbZcmp" CACHE STRING
    "Optional RV32ZC override passed to the Ibex DV Makefile. Empty means use IBEX_CONFIG value.")

# Snippy selection knobs.
set(SNIPPY_ITERATIONS 10 CACHE STRING
    "Number of Snippy runs for each selected YAML file")

set(SNIPPY_TEST "" CACHE STRING
    "Comma-separated list of Snippy YAML files to process, e.g. layout_arith,jalr,rem_div")

set(YAML_DIR "snippy/yaml_tests" CACHE PATH
    "Directory with Snippy YAML layout files. Relative paths are resolved from CORE_IBEX_ROOT")

# Snippy payload/link defaults.
# These values control how the Snippy-generated relocatable ELF is linked into
# the final test ELF.
set(SNIPPY_GCC_MARCH "rv32imc_zba_zbb_zbc_zbs_zicsr" CACHE STRING
    "RISC-V -march value used when linking Snippy-generated tests")

set(SNIPPY_GCC_MABI "ilp32" CACHE STRING
    "RISC-V -mabi value used when linking Snippy-generated tests")

set(BASE_LINKER_NAME "snippy_linker" CACHE STRING
    "Base linker script name without .elf.ld suffix")

set(TOOLCHAIN_ISA "rv32imcb" CACHE STRING
    "ISA string used by riscv-dv/Snippy GCC. Keep this in sync with IBEX_CONFIG/RV32ZC.")

# Custom Snippy RTL/UVM runner defaults.
set(SNIPPY_RTL_TEST "core_ibex_elf_manifest_test" CACHE STRING
    "UVM test name used for Snippy ELF layout simulations")

set(SNIPPY_TIMEOUT_S "7200" CACHE STRING
    "Timeout in seconds passed to the Snippy ELF layout UVM test")

set(SNIPPY_COV_SEED "1256" CACHE STRING
    "Fallback RTL simulator seed used for Snippy coverage runs")

option(FUNCTIONAL_COV "Enable functional coverage collection" OFF)

option(USE_URG_EXCLUDE
    "Use snippy/urg_exclude/urg_exclude_all.txt during VCS/URG coverage merge"
    ON
)

# Validate the required environment/tool settings.
if(NOT RISCV_GCC)
    message(FATAL_ERROR
        "RISCV_GCC is not set. "
        "Please export RISCV_GCC or pass -DRISCV_GCC=/path/to/gcc."
    )
endif()

if(NOT RISCV_OBJCOPY)
    message(FATAL_ERROR
        "RISCV_OBJCOPY is not set. "
        "Please export RISCV_OBJCOPY or pass -DRISCV_OBJCOPY=/path/to/objcopy."
    )
endif()

if(NOT SPIKE_PATH)
    message(FATAL_ERROR
        "SPIKE_PATH is not set. "
        "Please export SPIKE_PATH or pass -DSPIKE_PATH=/path/to/spike/bin."
    )
endif()

if(NOT PKG_CONFIG_PATH)
    message(FATAL_ERROR
        "PKG_CONFIG_PATH is not set. "
        "Please export PKG_CONFIG_PATH or pass -DPKG_CONFIG_PATH=/path/to/pkgconfig."
    )
endif()

if(NOT SNIPPY_ROOT)
    message(FATAL_ERROR
        "Environment variable SC_SNIPPY_PATH is not set. "
        "Please export SC_SNIPPY_PATH to the llvm-snippy installation root."
    )
endif()

# SNIPPY_ITERATIONS must stay a positive integer because it is used to build
# target names and run-index ranges.
if(NOT SNIPPY_ITERATIONS MATCHES "^[0-9]+$")
    message(FATAL_ERROR
        "SNIPPY_ITERATIONS must be a positive integer, got: ${SNIPPY_ITERATIONS}"
    )
endif()

if(NOT SNIPPY_ITERATIONS GREATER 0)
    message(FATAL_ERROR
        "SNIPPY_ITERATIONS must be greater than 0, got: ${SNIPPY_ITERATIONS}"
    )
endif()

# A fixed seed is optional, but if provided it must be numeric.
if(SEED AND NOT SEED MATCHES "^[0-9]+$")
    message(FATAL_ERROR
        "SEED must be empty or a non-negative integer, got: ${SEED}"
    )
endif()

# Validate Snippy/link/cosimulation defaults early.
if(NOT SNIPPY_GCC_MARCH)
    message(FATAL_ERROR "SNIPPY_GCC_MARCH must not be empty.")
endif()

if(NOT SNIPPY_GCC_MABI)
    message(FATAL_ERROR "SNIPPY_GCC_MABI must not be empty.")
endif()

if(NOT SNIPPY_TIMEOUT_S MATCHES "^[0-9]+$")
    message(FATAL_ERROR
        "SNIPPY_TIMEOUT_S must be a non-negative integer, got: ${SNIPPY_TIMEOUT_S}"
    )
endif()

if(NOT SNIPPY_COV_SEED MATCHES "^[0-9]+$")
    message(FATAL_ERROR
        "SNIPPY_COV_SEED must be a non-negative integer, got: ${SNIPPY_COV_SEED}"
    )
endif()

if(NOT SIGNATURE_ADDR MATCHES "^[0-9a-fA-F]+$")
    message(FATAL_ERROR
        "SIGNATURE_ADDR must be a hexadecimal value without 0x prefix, got: ${SIGNATURE_ADDR}"
    )
endif()

# Validate the simulator name early. The actual support is still determined by
# the Ibex DV Makefile and its simulator YAML.
set(VALID_SIMULATORS
    vcs
    xlm
    questa
    dsim
    riviera
    qrun
)

list(FIND VALID_SIMULATORS "${SIMULATOR}" SIMULATOR_INDEX)
if(SIMULATOR_INDEX EQUAL -1)
    message(FATAL_ERROR
        "Unsupported SIMULATOR='${SIMULATOR}'. "
        "Valid values: ${VALID_SIMULATORS}")
endif()

set(VALID_RV32ZC_VALUES
    ""
    ibex_pkg::RV32Zca
    ibex_pkg::RV32ZcaZcb
    ibex_pkg::RV32ZcaZcmp
    ibex_pkg::RV32ZcaZcbZcmp
)

list(FIND VALID_RV32ZC_VALUES "${RV32ZC}" RV32ZC_INDEX)
if(RV32ZC_INDEX EQUAL -1)
    message(FATAL_ERROR
        "Unsupported RV32ZC='${RV32ZC}'. "
        "Valid values: ${VALID_RV32ZC_VALUES}")
endif()

# Functional coverage only makes sense as part of the coverage-enabled flow.
if(FUNCTIONAL_COV AND NOT COV)
    message(FATAL_ERROR
        "FUNCTIONAL_COV=ON requires COV=ON."
    )
endif()

# LAST_ITER is used by foreach(iter RANGE ...).
math(EXPR LAST_ITER "${SNIPPY_ITERATIONS} - 1")
