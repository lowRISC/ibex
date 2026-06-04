# Top-level convenience targets for the flow.
#
# This file defines user-facing entry points:
#   - build_all / build_asm
#   - run_all
#   - clean_all / clean_ibex_make_out
#   - help_all
#
# The targets here do not implement the flow itself. They only aggregate
# lower-level targets defined in the other CMake files.

# Build both the generated assembler input and the RTL testbench.
set(BUILD_ALL_DEPS
    build_riscv_dv
    rtl_tb_compile
)

# Run all selected YAML targets.
add_custom_target(run_all
    DEPENDS ${ALL_YAML_TARGETS}
    COMMENT "Running all YAML files with ${SNIPPY_ITERATIONS} iterations each"
)

# Build the one-time prerequisites needed before running tests.
add_custom_target(build_all
    DEPENDS ${BUILD_ALL_DEPS}
    COMMENT "Building assembler and RTL testbench (one-time)"
)

# Build only the riscv-dv generated assembly.
add_custom_target(build_asm
    DEPENDS build_riscv_dv
    COMMENT "Building assembler"
)

# Some Ibex/riscv-dv helper goals generate files inside the source tree.
# Keep this list explicit so clean targets restore the checkout to a predictable
# state between configuration changes.
#
# riscv_core_setting.sv is produced by the Ibex core_config Make goal and is
# required by riscv-dv when generating the bootstrap assembly used by this
# Snippy flow.
set(CLEAN_SOURCE_TREE_FILES
    "${CORE_IBEX_ROOT}/riscv_dv_extension/riscv_core_setting.sv"
)

# There are two Ibex Make output trees in this flow:
#
#   OUT
#       Main output used by rtl_tb_compile, snippy_rtl_sim_run and coverage.
#       This is where the real RTL simulation metadata, test runs, logs and
#       coverage outputs live.
#
#   ${CMAKE_BINARY_DIR}/ibex_core_config_out
#       Temporary metadata sandbox used only by GOAL=core_config while preparing
#       riscv_core_setting.sv for riscv-dv assembly generation.
#
# core_config must run before riscv-dv generation, but its metadata should not
# be mixed with the main RTL simulation metadata. Both output trees are
# configuration-sensitive and must be removed by clean targets.

# clean_all must not depend on COV or other configuration knobs.
#
# It is commonly run before reconfiguring CMake with a different set of options.
# Therefore it must remove all configuration-sensitive generated outputs,
# including:
#   - main Ibex Make output,
#   - core_config-only Ibex Make output,
#   - generated riscv-dv assembly,
#   - Snippy test outputs,
#   - summary files.
#
# Keep only heavy reusable artifacts that are independent from this flow.
set(CLEAN_KEEP_NAMES
    Release
)

# Build the find command used by clean_all.
set(CLEAN_FIND_ARGS
    "${CMAKE_BINARY_DIR}"
    -mindepth 1
    -maxdepth 1
)

foreach(_keep_name ${CLEAN_KEEP_NAMES})
    list(APPEND CLEAN_FIND_ARGS -not -name "${_keep_name}")
endforeach()

list(APPEND CLEAN_FIND_ARGS -exec rm -rf {} +)

# Remove generated files while keeping selected reusable directories.
add_custom_target(clean_all
    COMMAND ${CMAKE_COMMAND} -E remove_directory "${CMAKE_BINARY_DIR}/_CPack_Packages"

    # Remove build-tree outputs except selected reusable directories. Since only
    # Release is kept, this removes both OUT and ibex_core_config_out.
    COMMAND find ${CLEAN_FIND_ARGS}

    # Remove generated files that the Ibex Make/riscv-dv helper flow writes into
    # the source tree.
    COMMAND ${CMAKE_COMMAND} -E remove -f ${CLEAN_SOURCE_TREE_FILES}

    COMMENT "Cleaning generated files, please re-run cmake if needed"
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    VERBATIM
)

# Smaller explicit cleanup target for cases where only Ibex Make outputs and
# generated riscv-dv settings should be dropped.
#
# This removes both:
#   - the main simulation OUT,
#   - the core_config-only OUT.
add_custom_target(clean_ibex_make_out
    COMMAND ${CMAKE_COMMAND} -E remove_directory "${OUT}"
    COMMAND ${CMAKE_COMMAND} -E remove_directory "${CMAKE_BINARY_DIR}/ibex_core_config_out"
    COMMAND ${CMAKE_COMMAND} -E remove -f ${CLEAN_SOURCE_TREE_FILES}
    COMMENT "Cleaning Ibex Make outputs and generated riscv-dv settings"
    VERBATIM
)

# Print a short overview of the main entry points in this flow.
add_custom_target(help_all
    COMMAND ${CMAKE_COMMAND} -E echo "Available targets:"
    COMMAND ${CMAKE_COMMAND} -E echo "  build_all            - Build assembler and RTL testbench"
    COMMAND ${CMAKE_COMMAND} -E echo "  build_asm            - Build assembler"
    COMMAND ${CMAKE_COMMAND} -E echo "  run_all              - Run all tests"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Coverage targets (require -DCOV=ON):"
    COMMAND ${CMAKE_COMMAND} -E echo "  coverage_functional  - Generate functional coverage report (requires -DFUNCTIONAL_COV=ON)"
    COMMAND ${CMAKE_COMMAND} -E echo "  coverage_merged      - Generate merged coverage report"
    COMMAND ${CMAKE_COMMAND} -E echo "  coverage             - Generate configured coverage report(s)"
    COMMAND ${CMAKE_COMMAND} -E echo ""
    COMMAND ${CMAKE_COMMAND} -E echo "Clean targets:"
    COMMAND ${CMAKE_COMMAND} -E echo "  clean_all            - Clean generated files"
    COMMAND ${CMAKE_COMMAND} -E echo "  clean_ibex_make_out  - Clean Ibex Make outputs and generated riscv-dv settings"
    COMMENT "Show help message"
    VERBATIM
)
