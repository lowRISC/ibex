# Build the Ibex RTL testbench/simulator using the upstream Ibex UVM DV Makefile.
#
# The selected RTL simulator is controlled by Ibex's SIMULATOR knob:
#
#   SIMULATOR=${SIMULATOR}
#
# CMake does not assemble simulator-specific compile commands directly. It only
# delegates the compile step to dv/uvm/core_ibex/Makefile:
#
#   make run GOAL=rtl_tb_compile
#
# The primary target is `rtl_tb_compile`.

set(IBEX_MAKE_METADATA_DIR "${OUT}/metadata")
set(RTL_TB_COMPILE_STAMP "${IBEX_MAKE_METADATA_DIR}/tb.compile.stamp")

set(IBEX_MAKE_COSIM 1)

ibex_make_env(IBEX_MAKE_ENV)
ibex_make_common_args(IBEX_MAKE_COMMON_ARGS)

set(IBEX_MAKE_ARGS
    run
    GOAL=rtl_tb_compile
    ${IBEX_MAKE_COMMON_ARGS}
    COSIM=${IBEX_MAKE_COSIM}
)

ibex_make_append_rv32zc_arg(IBEX_MAKE_ARGS)

if(COV)
    set(RTL_TB_COMPILE_COV 1)
else()
    set(RTL_TB_COMPILE_COV 0)
endif()

set(RTL_TB_COMPILE_COMMENT
    "Ibex make rtl_tb_compile (${SIMULATOR}, TEST=${TEST}, COV=${RTL_TB_COMPILE_COV}, IBEX_CONFIG=${IBEX_CONFIG}")

if(RV32ZC)
    set(RTL_TB_COMPILE_COMMENT
        "${RTL_TB_COMPILE_COMMENT}, RV32ZC=${RV32ZC}")
endif()

set(RTL_TB_COMPILE_COMMENT "${RTL_TB_COMPILE_COMMENT})")

add_custom_command(
    OUTPUT  ${RTL_TB_COMPILE_STAMP}
    COMMAND ${CMAKE_COMMAND} -E make_directory "${DIR_LOG}" "${OUT}"
    COMMAND ${CMAKE_COMMAND} -E env
            ${IBEX_MAKE_ENV}
            ${IBEX_MAKE_PROGRAM}
            ${IBEX_MAKE_ARGS}
    WORKING_DIRECTORY "${CORE_IBEX_ROOT}"
    DEPENDS build_riscv_dv
    COMMENT "${RTL_TB_COMPILE_COMMENT}"
    VERBATIM
)

add_custom_target(rtl_tb_compile
    DEPENDS ${RTL_TB_COMPILE_STAMP}
    COMMENT "Build RTL testbench/simulator via Ibex Makefile"
)

add_dependencies(rtl_tb_compile build_riscv_dv)
