# Define per-YAML Snippy generation targets.
#
# For each selected layout YAML, this file creates:
#   1. one target per iteration,
#   2. one aggregate target per YAML,
#   3. the final list of YAML run targets consumed by run_all.
#
# The per-iteration build stages are defined in SnippyCommands.cmake.

function(add_yaml_target yaml_file)
    get_filename_component(YAML_NAME_WE ${yaml_file} NAME_WE)

    set(YAML_BASE_DIR "${DIR_TESTS}/${YAML_NAME_WE}")
    set(YAML_ITER_TARGETS "")

    foreach(iter RANGE ${LAST_ITER})
        ibex_snippy_add_iteration_target(
            ${yaml_file}
            ${YAML_NAME_WE}
            ${YAML_BASE_DIR}
            ${iter}
            ITER_TARGET
        )

        list(APPEND YAML_ITER_TARGETS ${ITER_TARGET})
    endforeach()

    add_custom_target(run_all_${YAML_NAME_WE}
        DEPENDS ${YAML_ITER_TARGETS}
        COMMENT "Running all ${SNIPPY_ITERATIONS} iterations for ${YAML_NAME_WE}"
    )

    add_dependencies(run_all_${YAML_NAME_WE} build_riscv_dv rtl_tb_compile)

    set(ALL_YAML_TARGETS ${ALL_YAML_TARGETS} run_all_${YAML_NAME_WE} PARENT_SCOPE)
endfunction()

# Instantiate targets for all selected YAML files.
set(ALL_YAML_TARGETS "")
foreach(yaml_file ${YAML_FILES})
    add_yaml_target(${yaml_file})
endforeach()
