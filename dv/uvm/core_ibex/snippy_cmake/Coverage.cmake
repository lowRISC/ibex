# Coverage report targets for the Snippy + Ibex flow.
#
# CMake does not invoke simulator-specific coverage tools directly.
# Snippy runs export standard Ibex TestRunResult-compatible artifacts and
# register them through:
#
#   ${METADATA-DIR}/snippy_tests.mk
#
# Therefore coverage can use the standard Ibex Make goals:
#
#   riscv_dv_fcov
#   merge_cov
#
# An optional coverage exclude/waiver file can be enabled through
# USE_URG_EXCLUDE. When enabled, CMake forwards COV_EXCLUDE_FILE to the Ibex Make
# flow as VCS_URG_ELFILE, where merge_cov.py passes it to URG as:
#
#   urg ... -elfile <file>
#
# COV_EXCLUDE_TESTS is used to keep placeholder/testlist entries, such as
# snippy_func_test, out of the coverage dependency graph while still using the
# standard Ibex coverage scripts.
#
# Important: coverage targets intentionally do not depend on run_all.
# The expected flow is:
#
#   cmake --build build --target run_all
#   cmake --build build --target coverage
#
# This keeps test execution and coverage collection as separate stages.

if(COV)

    set(COV_EXCLUDE_MAKE_ARGS "")

    if(USE_URG_EXCLUDE)
        set(COV_EXCLUDE_FILE "${URG_EXCLUDE}/urg_exclude_all.txt" CACHE FILEPATH
            "Coverage exclude/waiver file used by simulator-specific coverage merge tools.")

        if(NOT EXISTS "${COV_EXCLUDE_FILE}")
            message(FATAL_ERROR "Coverage exclude file not found: ${COV_EXCLUDE_FILE}")
        endif()

        if(SIMULATOR STREQUAL "vcs")
            list(APPEND COV_EXCLUDE_MAKE_ARGS
                "VCS_URG_ELFILE=${COV_EXCLUDE_FILE}"
            )
        endif()
    endif()

    ibex_make_env(IBEX_MAKE_ENV)
    ibex_make_common_args(IBEX_COV_COMMON_ARGS)

    set(IBEX_COV_MAKE_BASE_ARGS
        run_existing_metadata
        ${IBEX_COV_COMMON_ARGS}
        COV_EXCLUDE_TESTS=snippy_func_test
        ${COV_EXCLUDE_MAKE_ARGS}
    )

    ibex_make_append_rv32zc_arg(IBEX_COV_MAKE_BASE_ARGS)

    if(FUNCTIONAL_COV)
        add_custom_target(coverage_functional
            # Make's riscv_dv_fcov target is stamp-based. Remove the stamp so a
            # repeated CMake coverage invocation regenerates functional coverage
            # and picks up COV_EXCLUDE_TESTS changes.
            COMMAND ${CMAKE_COMMAND} -E remove -f
                    "${OUT}/metadata/fcov.stamp"
            COMMAND ${CMAKE_COMMAND} -E env
                    ${IBEX_MAKE_ENV}
                    ${IBEX_MAKE_PROGRAM}
                    ${IBEX_COV_MAKE_BASE_ARGS}
                    GOAL=riscv_dv_fcov
            WORKING_DIRECTORY "${CORE_IBEX_ROOT}"
            COMMENT "Generating functional coverage through Ibex Make"
            VERBATIM
        )

        add_custom_target(coverage_merged
            DEPENDS coverage_functional
            # Make's merge_cov target is stamp-based. Remove the stamp so a
            # repeated CMake coverage invocation regenerates the report and
            # picks up changes to coverage exclude settings.
            COMMAND ${CMAKE_COMMAND} -E remove -f
                    "${OUT}/metadata/merge.cov.stamp"
            COMMAND ${CMAKE_COMMAND} -E env
                    ${IBEX_MAKE_ENV}
                    ${IBEX_MAKE_PROGRAM}
                    ${IBEX_COV_MAKE_BASE_ARGS}
                    GOAL=merge_cov
            WORKING_DIRECTORY "${CORE_IBEX_ROOT}"
            COMMENT "Generating merged coverage through Ibex Make"
            VERBATIM
        )

        add_custom_target(coverage
            DEPENDS coverage_merged
            COMMAND ${CMAKE_COMMAND} -E echo "Coverage reports generated:"
            COMMAND ${CMAKE_COMMAND} -E echo "  Functional: ${COV_REPORT_DIR}/functional/index.html"
            COMMAND ${CMAKE_COMMAND} -E echo "  Merged: ${COV_REPORT_DIR}/index.html"
            COMMENT "All coverage reports generated"
            VERBATIM
        )
    else()
        add_custom_target(coverage_merged
            COMMAND ${CMAKE_COMMAND} -E remove -f
                    "${OUT}/metadata/merge.cov.stamp"
            COMMAND ${CMAKE_COMMAND} -E env
                    ${IBEX_MAKE_ENV}
                    ${IBEX_MAKE_PROGRAM}
                    ${IBEX_COV_MAKE_BASE_ARGS}
                    GOAL=merge_cov
            WORKING_DIRECTORY "${CORE_IBEX_ROOT}"
            COMMENT "Generating RTL coverage through Ibex Make"
            VERBATIM
        )

        add_custom_target(coverage
            DEPENDS coverage_merged
            COMMAND ${CMAKE_COMMAND} -E echo "Coverage report generated: ${COV_REPORT_DIR}/index.html"
            COMMENT "Coverage report generated"
            VERBATIM
        )
    endif()

endif()
