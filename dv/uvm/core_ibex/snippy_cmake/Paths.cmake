# Resolve all external tool paths, source inputs and build directories.
#
# This file:
#   - derives full paths from the configured roots,
#   - validates that required files and directories exist,
#   - defines the main build/output directories used by the flow.
#
# CMAKE_CURRENT_SOURCE_DIR is expected to be:
#
#   ibex/dv/uvm/core_ibex
#
# Snippy-specific inputs are expected under:
#
#   ibex/dv/uvm/core_ibex/snippy/

# Full paths to external tools and core source directories.
set(SNIPPY_EXE          "${SNIPPY_ROOT}/llvm-snippy")
set(SNIPPY_ELF_PARSER   "${CORE_IBEX_ROOT}/riscv_dv_extension/snippy_elf_parser.py")
set(SNIPPY_LOG_ANALYZER "${CORE_IBEX_ROOT}/scripts/analyze_snippy_log.py")

# Snippy input root inside core_ibex.
set(SNIPPY_INPUT_ROOT "${CORE_IBEX_ROOT}/snippy")

# Snippy CMake helper scripts.
set(SNIPPY_CMAKE_ROOT "${CORE_IBEX_ROOT}/snippy_cmake")
set(SNIPPY_CMAKE_SCRIPT_DIR "${SNIPPY_CMAKE_ROOT}/scripts")

set(GENERATE_SNIPPY_LINKER_SCRIPT
    "${SNIPPY_CMAKE_SCRIPT_DIR}/GenerateSnippyLinker.cmake")

# Paths to source inputs consumed by the flow.
set(TESTLIST             "${CORE_IBEX_ROOT}/riscv_dv_extension/testlist.yaml")
set(CUSTOM_TARGET        "${CORE_IBEX_ROOT}/riscv_dv_extension")
set(CSR_YAML             "${CORE_IBEX_ROOT}/riscv_dv_extension/csr_description.yaml")
set(LD_ORIGIN_SCRIPT_SRC "${SNIPPY_INPUT_ROOT}/linker/${BASE_LINKER_NAME}.elf.ld")
set(ASM_FILE             "${SNIPPY_INPUT_ROOT}/asm_func/illegal_opcodes.s")
set(URG_EXCLUDE          "${SNIPPY_INPUT_ROOT}/urg_exclude")

if(IS_ABSOLUTE "${YAML_DIR}")
    set(YAML_DIR_RESOLVED "${YAML_DIR}")
else()
    set(YAML_DIR_RESOLVED "${CORE_IBEX_ROOT}/${YAML_DIR}")
endif()
set(YAML_DIR "${YAML_DIR_RESOLVED}")

# Validate the main roots, tool binaries and input files before the build graph
# is created.
if(NOT EXISTS "${IBEX_ROOT}")
    message(FATAL_ERROR "IBEX_ROOT does not exist: ${IBEX_ROOT}")
endif()

if(NOT EXISTS "${CORE_IBEX_ROOT}")
    message(FATAL_ERROR "CORE_IBEX_ROOT does not exist: ${CORE_IBEX_ROOT}")
endif()

if(NOT EXISTS "${SNIPPY_INPUT_ROOT}")
    message(FATAL_ERROR "SNIPPY_INPUT_ROOT does not exist: ${SNIPPY_INPUT_ROOT}")
endif()

if(NOT EXISTS "${SNIPPY_CMAKE_ROOT}")
    message(FATAL_ERROR "SNIPPY_CMAKE_ROOT does not exist: ${SNIPPY_CMAKE_ROOT}")
endif()

if(NOT EXISTS "${SNIPPY_CMAKE_SCRIPT_DIR}")
    message(FATAL_ERROR "SNIPPY_CMAKE_SCRIPT_DIR does not exist: ${SNIPPY_CMAKE_SCRIPT_DIR}")
endif()

if(NOT EXISTS "${GENERATE_SNIPPY_LINKER_SCRIPT}")
    message(FATAL_ERROR "GenerateSnippyLinker script not found: ${GENERATE_SNIPPY_LINKER_SCRIPT}")
endif()

if(NOT EXISTS "${SNIPPY_ELF_PARSER}")
    message(FATAL_ERROR "Snippy ELF parser not found: ${SNIPPY_ELF_PARSER}")
endif()

if(NOT EXISTS "${SNIPPY_LOG_ANALYZER}")
    message(FATAL_ERROR "Snippy log analyzer not found: ${SNIPPY_LOG_ANALYZER}")
endif()

if(NOT EXISTS "${RISCV_GCC}")
    message(FATAL_ERROR "RISCV_GCC executable not found: ${RISCV_GCC}")
endif()

if(NOT EXISTS "${RISCV_OBJCOPY}")
    message(FATAL_ERROR "RISCV_OBJCOPY executable not found: ${RISCV_OBJCOPY}")
endif()

if(NOT EXISTS "${SPIKE_PATH}")
    message(FATAL_ERROR "SPIKE_PATH does not exist: ${SPIKE_PATH}")
endif()

if(NOT EXISTS "${SNIPPY_EXE}")
    message(FATAL_ERROR "llvm-snippy not found: ${SNIPPY_EXE}")
endif()

if(NOT EXISTS "${TESTLIST}")
    message(FATAL_ERROR "riscv-dv testlist not found: ${TESTLIST}")
endif()

if(NOT EXISTS "${CUSTOM_TARGET}")
    message(FATAL_ERROR "riscv-dv custom target directory not found: ${CUSTOM_TARGET}")
endif()

if(NOT EXISTS "${CSR_YAML}")
    message(FATAL_ERROR "CSR YAML not found: ${CSR_YAML}")
endif()

if(NOT EXISTS "${LD_ORIGIN_SCRIPT_SRC}")
    message(FATAL_ERROR "Base linker script not found: ${LD_ORIGIN_SCRIPT_SRC}")
endif()

if(NOT EXISTS "${YAML_DIR}")
    message(FATAL_ERROR "YAML directory not found: ${YAML_DIR}")
endif()

if(NOT EXISTS "${ASM_FILE}")
    message(FATAL_ERROR "ASM helper file not found: ${ASM_FILE}")
endif()

if(USE_URG_EXCLUDE AND NOT EXISTS "${URG_EXCLUDE}")
    message(FATAL_ERROR "URG exclude directory not found: ${URG_EXCLUDE}")
endif()

# Keep a copy of the base linker script in the build tree. The per-iteration
# linker scripts are generated later under tests/<layout>/<layout>_<iter>/linker.
set(BASE_LINKER_BUILD_DIR "${CMAKE_BINARY_DIR}/linker_template")
file(COPY "${LD_ORIGIN_SCRIPT_SRC}" DESTINATION "${BASE_LINKER_BUILD_DIR}/")
set(LD_SCRIPT_SRC "${BASE_LINKER_BUILD_DIR}/${BASE_LINKER_NAME}.elf.ld")

# Ibex Make output directory used by the main RTL compile/simulation/coverage
# flow. The preparation-only core_config step uses a separate OUT directory in
# RiscvDv.cmake to avoid mixing its metadata with the main simulation metadata.
#
# In standalone mode this defaults to a local build-tree output.
# When called from the Ibex Makefile, pass:
#
#   -DOUT=$(OUT-DIR)
#
set(OUT "${CMAKE_BINARY_DIR}/ibex_make_out" CACHE PATH
    "Output directory passed as OUT=... to the Ibex DV Makefile")

# Use the same coverage layout as the upstream Ibex DV Makefile.
# This avoids creating one coverage database through Ibex Make and another one
# through the CMake flow.
set(COVERAGE_DIR   "${OUT}/run/coverage")
set(FCOV_DIR       "${COVERAGE_DIR}/fcov")
set(SHARED_COV_DIR "${COVERAGE_DIR}/shared_cov")
set(COV_REPORT_DIR "${COVERAGE_DIR}/report")

# Single shared RTL coverage database used by the selected simulator backend.
set(MASTER_VDB  "${SHARED_COV_DIR}/test.vdb")
set(RTL_RUN_VDB "${MASTER_VDB}")

# Main build directories used by the flow.
set(DIR_DV      "${CMAKE_BINARY_DIR}/dv")
set(DIR_LOG     "${CMAKE_BINARY_DIR}/log")
set(DIR_SUMMARY "${CMAKE_BINARY_DIR}/summary")
set(DIR_TESTS   "${CMAKE_BINARY_DIR}/tests")

# Create the top-level output directories up front.
#
# Coverage subdirectories are created only for COV=ON. The per-test trace files
# such as rtl_trace.csv are normal run artifacts and may still appear when
# COV=OFF.
file(MAKE_DIRECTORY
    ${DIR_DV}
    ${DIR_LOG}
    ${DIR_SUMMARY}
    ${DIR_TESTS}
    ${OUT}
    ${BASE_LINKER_BUILD_DIR}
)

if(COV)
    file(MAKE_DIRECTORY
        ${COVERAGE_DIR}
        ${FCOV_DIR}
        ${SHARED_COV_DIR}
        ${COV_REPORT_DIR}
        ${MASTER_VDB}
    )
endif()
