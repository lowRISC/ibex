# Resolve the set of YAML inputs used by this build.
#
# This file:
#   1. discovers all available layout_*.yaml files,
#   2. optionally filters them using SNIPPY_TEST,
#   3. creates cover.cfg if it does not exist yet.

# Collect all layout YAMLs available in the source tree.
file(GLOB ALL_YAML_FILES "${YAML_DIR}/layout_*.yaml")
if(NOT ALL_YAML_FILES)
    message(FATAL_ERROR "No layout_*.yaml files found in ${YAML_DIR}")
endif()

# Either use the full set or reduce it according to SNIPPY_TEST.
if(SNIPPY_TEST)
    ibex_snippy_select_yaml_files("${YAML_DIR}" "${SNIPPY_TEST}" YAML_FILES)

    if(NOT YAML_FILES)
        message(FATAL_ERROR "No valid YAML files found matching the filter: ${SNIPPY_TEST}")
    endif()
else()
    set(YAML_FILES ${ALL_YAML_FILES})
endif()

message(STATUS "Selected YAML files: ${YAML_FILES}")

# The cover.cfg file is needed by the coverage-enabled VCS flow.
set(COVER_CFG "${CORE_IBEX_ROOT}/cover.cfg")
if(NOT EXISTS "${COVER_CFG}")
    file(WRITE "${COVER_CFG}"
"+tree tb_top
+tree core_ibex_tb_top
+module ibex_top
+tree core_ibex_tb_top.dut.*
")
    message(STATUS "Created ${COVER_CFG}")
endif()
