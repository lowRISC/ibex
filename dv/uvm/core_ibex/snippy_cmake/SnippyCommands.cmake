# Per-iteration command helpers for the custom Snippy flow.
#
# This file owns the individual build stages for one Snippy iteration:
#   - llvm-snippy generation,
#   - linker script generation,
#   - GCC link,
#   - ELF layout generation,
#   - RTL/ISS cosimulation target wiring.
#
# The higher-level YAML/iteration orchestration lives in Snippy.cmake.

# Add the llvm-snippy generation command for one iteration.
#
# Outputs:
#   - SNIPPY_ELF
#   - SNIPPY_LOG
function(ibex_snippy_add_generation_command)
    set(options)
    set(oneValueArgs
        YAML_FILE
        YAML_NAME
        ITER
        SNIPPY_ELF
        SNIPPY_LOG
    )
    cmake_parse_arguments(SNIPPY_GEN "${options}" "${oneValueArgs}" "" ${ARGN})

    if(NOT SNIPPY_GEN_YAML_FILE)
        message(FATAL_ERROR "ibex_snippy_add_generation_command: YAML_FILE is required")
    endif()

    if(NOT SNIPPY_GEN_YAML_NAME)
        message(FATAL_ERROR "ibex_snippy_add_generation_command: YAML_NAME is required")
    endif()

    if(NOT DEFINED SNIPPY_GEN_ITER)
        message(FATAL_ERROR "ibex_snippy_add_generation_command: ITER is required")
    endif()

    if(NOT SNIPPY_GEN_SNIPPY_ELF)
        message(FATAL_ERROR "ibex_snippy_add_generation_command: SNIPPY_ELF is required")
    endif()

    if(NOT SNIPPY_GEN_SNIPPY_LOG)
        message(FATAL_ERROR "ibex_snippy_add_generation_command: SNIPPY_LOG is required")
    endif()

    add_custom_command(
        OUTPUT
            ${SNIPPY_GEN_SNIPPY_ELF}
            ${SNIPPY_GEN_SNIPPY_LOG}
        COMMAND ${SNIPPY_EXE}
                --last-instr=RET
                ${SNIPPY_GEN_YAML_FILE}
                -o ${SNIPPY_GEN_SNIPPY_ELF}
                &> ${SNIPPY_GEN_SNIPPY_LOG}
        DEPENDS ${SNIPPY_GEN_YAML_FILE}
        COMMENT "llvm-snippy for ${SNIPPY_GEN_YAML_NAME}, iter ${SNIPPY_GEN_ITER} → ${SNIPPY_GEN_SNIPPY_ELF}"
        VERBATIM
    )
endfunction()

# Add the generated linker script command for one iteration.
#
# Outputs:
#   - LINKER_SCRIPT
function(ibex_snippy_add_linker_command)
    set(options)
    set(oneValueArgs
        YAML_NAME
        ITER
        SNIPPY_ELF
        LINKER_SCRIPT
    )
    cmake_parse_arguments(SNIPPY_LINKER "${options}" "${oneValueArgs}" "" ${ARGN})

    if(NOT SNIPPY_LINKER_YAML_NAME)
        message(FATAL_ERROR "ibex_snippy_add_linker_command: YAML_NAME is required")
    endif()

    if(NOT DEFINED SNIPPY_LINKER_ITER)
        message(FATAL_ERROR "ibex_snippy_add_linker_command: ITER is required")
    endif()

    if(NOT SNIPPY_LINKER_SNIPPY_ELF)
        message(FATAL_ERROR "ibex_snippy_add_linker_command: SNIPPY_ELF is required")
    endif()

    if(NOT SNIPPY_LINKER_LINKER_SCRIPT)
        message(FATAL_ERROR "ibex_snippy_add_linker_command: LINKER_SCRIPT is required")
    endif()

    add_custom_command(
        OUTPUT ${SNIPPY_LINKER_LINKER_SCRIPT}
        COMMAND ${CMAKE_COMMAND}
                -DINPUT_LD=${LD_ORIGIN_SCRIPT_SRC}
                -DOUTPUT_LD=${SNIPPY_LINKER_LINKER_SCRIPT}
                -DSNIPPY_ELF=${SNIPPY_LINKER_SNIPPY_ELF}
                -P ${GENERATE_SNIPPY_LINKER_SCRIPT}
        DEPENDS ${SNIPPY_LINKER_SNIPPY_ELF} ${LD_ORIGIN_SCRIPT_SRC}
        COMMENT "Generate linker script for ${SNIPPY_LINKER_YAML_NAME}, iter ${SNIPPY_LINKER_ITER} → ${SNIPPY_LINKER_LINKER_SCRIPT}"
        VERBATIM
    )
endfunction()

# Build the list of object/input files for the GCC link step.
#
# layout_illegal additionally links a hand-written assembly helper.
function(ibex_snippy_get_gcc_inputs yaml_name snippy_elf out_var)
    set(_gcc_inputs
        ${GEN_ASM}
        ${snippy_elf}
    )

    if(${yaml_name} STREQUAL "layout_illegal")
        list(PREPEND _gcc_inputs ${ASM_FILE})
    endif()

    set(${out_var} "${_gcc_inputs}" PARENT_SCOPE)
endfunction()

# Add the GCC link command for one iteration.
#
# Outputs:
#   - LINKED_ELF
#   - GCC_LOG
function(ibex_snippy_add_link_command)
    set(options)
    set(oneValueArgs
        YAML_NAME
        ITER
        SNIPPY_ELF
        LINKER_SCRIPT
        LINKED_ELF
        GCC_LOG
    )
    cmake_parse_arguments(SNIPPY_LINK "${options}" "${oneValueArgs}" "" ${ARGN})

    if(NOT SNIPPY_LINK_YAML_NAME)
        message(FATAL_ERROR "ibex_snippy_add_link_command: YAML_NAME is required")
    endif()

    if(NOT DEFINED SNIPPY_LINK_ITER)
        message(FATAL_ERROR "ibex_snippy_add_link_command: ITER is required")
    endif()

    if(NOT SNIPPY_LINK_SNIPPY_ELF)
        message(FATAL_ERROR "ibex_snippy_add_link_command: SNIPPY_ELF is required")
    endif()

    if(NOT SNIPPY_LINK_LINKER_SCRIPT)
        message(FATAL_ERROR "ibex_snippy_add_link_command: LINKER_SCRIPT is required")
    endif()

    if(NOT SNIPPY_LINK_LINKED_ELF)
        message(FATAL_ERROR "ibex_snippy_add_link_command: LINKED_ELF is required")
    endif()

    if(NOT SNIPPY_LINK_GCC_LOG)
        message(FATAL_ERROR "ibex_snippy_add_link_command: GCC_LOG is required")
    endif()

    set(COMMON_GCC_ARGS
        -march=${SNIPPY_GCC_MARCH}
        -mabi=${SNIPPY_GCC_MABI}
        -nostdlib
        -mno-relax
    )

    ibex_snippy_get_gcc_inputs(
        ${SNIPPY_LINK_YAML_NAME}
        ${SNIPPY_LINK_SNIPPY_ELF}
        GCC_INPUTS
    )

    ibex_snippy_add_gcc_link_command(
        OUTPUT ${SNIPPY_LINK_LINKED_ELF}
        LOG ${SNIPPY_LINK_GCC_LOG}
        LINKER_SCRIPT ${SNIPPY_LINK_LINKER_SCRIPT}
        INPUTS ${GCC_INPUTS}
        DEPENDS build_riscv_dv ${SNIPPY_LINK_SNIPPY_ELF} ${SNIPPY_LINK_LINKER_SCRIPT}
        GCC_ARGS ${COMMON_GCC_ARGS}
        COMMENT "GCC link for ${SNIPPY_LINK_YAML_NAME}, iter ${SNIPPY_LINK_ITER} → ${SNIPPY_LINK_LINKED_ELF}"
    )
endfunction()

# Add the ELF layout generation command for one iteration.
#
# Outputs:
#   - ELF_LAYOUT_JSON
#   - ELF_LAYOUT_SVLOAD
#   - ELF_LAYOUT_LOG
function(ibex_snippy_add_elf_layout_command)
    set(options)
    set(oneValueArgs
        YAML_NAME
        ITER
        LINKED_ELF
        ELF_LAYOUT_JSON
        ELF_LAYOUT_SVLOAD
        ELF_LAYOUT_LOG
    )
    cmake_parse_arguments(ELF_LAYOUT "${options}" "${oneValueArgs}" "" ${ARGN})

    if(NOT ELF_LAYOUT_YAML_NAME)
        message(FATAL_ERROR "ibex_snippy_add_elf_layout_command: YAML_NAME is required")
    endif()

    if(NOT DEFINED ELF_LAYOUT_ITER)
        message(FATAL_ERROR "ibex_snippy_add_elf_layout_command: ITER is required")
    endif()

    if(NOT ELF_LAYOUT_LINKED_ELF)
        message(FATAL_ERROR "ibex_snippy_add_elf_layout_command: LINKED_ELF is required")
    endif()

    if(NOT ELF_LAYOUT_ELF_LAYOUT_JSON)
        message(FATAL_ERROR "ibex_snippy_add_elf_layout_command: ELF_LAYOUT_JSON is required")
    endif()

    if(NOT ELF_LAYOUT_ELF_LAYOUT_SVLOAD)
        message(FATAL_ERROR "ibex_snippy_add_elf_layout_command: ELF_LAYOUT_SVLOAD is required")
    endif()

    if(NOT ELF_LAYOUT_ELF_LAYOUT_LOG)
        message(FATAL_ERROR "ibex_snippy_add_elf_layout_command: ELF_LAYOUT_LOG is required")
    endif()

    add_custom_command(
        OUTPUT
            ${ELF_LAYOUT_ELF_LAYOUT_JSON}
            ${ELF_LAYOUT_ELF_LAYOUT_SVLOAD}
        COMMAND python3
                ${SNIPPY_ELF_PARSER}
                ${ELF_LAYOUT_LINKED_ELF}
                --json-out ${ELF_LAYOUT_ELF_LAYOUT_JSON}
                --sv-out ${ELF_LAYOUT_ELF_LAYOUT_SVLOAD}
                &> ${ELF_LAYOUT_ELF_LAYOUT_LOG}
        DEPENDS ${ELF_LAYOUT_LINKED_ELF}
        BYPRODUCTS ${ELF_LAYOUT_ELF_LAYOUT_LOG}
        COMMENT "Generate ELF layout for ${ELF_LAYOUT_YAML_NAME}, iter ${ELF_LAYOUT_ITER} → ${ELF_LAYOUT_ELF_LAYOUT_SVLOAD}"
        VERBATIM
    )
endfunction()

# Add the RTL/ISS cosimulation target for one iteration.
function(ibex_snippy_add_cosim_target)
    set(options)
    set(oneValueArgs
        TARGET_NAME
        YAML_NAME
        ITER
        ITER_DIR
        LINKED_ELF
        ELF_LAYOUT_SVLOAD
        SNIPPY_LOG
    )
    cmake_parse_arguments(SNIPPY_COSIM "${options}" "${oneValueArgs}" "" ${ARGN})

    if(NOT SNIPPY_COSIM_TARGET_NAME)
        message(FATAL_ERROR "ibex_snippy_add_cosim_target: TARGET_NAME is required")
    endif()

    if(NOT SNIPPY_COSIM_YAML_NAME)
        message(FATAL_ERROR "ibex_snippy_add_cosim_target: YAML_NAME is required")
    endif()

    if(NOT DEFINED SNIPPY_COSIM_ITER)
        message(FATAL_ERROR "ibex_snippy_add_cosim_target: ITER is required")
    endif()

    if(NOT SNIPPY_COSIM_ITER_DIR)
        message(FATAL_ERROR "ibex_snippy_add_cosim_target: ITER_DIR is required")
    endif()

    if(NOT SNIPPY_COSIM_LINKED_ELF)
        message(FATAL_ERROR "ibex_snippy_add_cosim_target: LINKED_ELF is required")
    endif()

    if(NOT SNIPPY_COSIM_ELF_LAYOUT_SVLOAD)
        message(FATAL_ERROR "ibex_snippy_add_cosim_target: ELF_LAYOUT_SVLOAD is required")
    endif()

    if(NOT SNIPPY_COSIM_SNIPPY_LOG)
        message(FATAL_ERROR "ibex_snippy_add_cosim_target: SNIPPY_LOG is required")
    endif()

    ibex_add_cosimulation_target(
        TARGET_NAME ${SNIPPY_COSIM_TARGET_NAME}
        YAML_NAME ${SNIPPY_COSIM_YAML_NAME}
        ITER ${SNIPPY_COSIM_ITER}
        ITER_DIR ${SNIPPY_COSIM_ITER_DIR}
        LINKED_ELF ${SNIPPY_COSIM_LINKED_ELF}
        ELF_LAYOUT ${SNIPPY_COSIM_ELF_LAYOUT_SVLOAD}
        SNIPPY_LOG ${SNIPPY_COSIM_SNIPPY_LOG}
    )
endfunction()

# Add all commands and the run target for one YAML iteration.
function(ibex_snippy_add_iteration_target yaml_file yaml_name yaml_base_dir iter out_var)
    ibex_snippy_init_iteration_layout(
        "${yaml_base_dir}"
        "${yaml_name}"
        "${iter}"
    )

    set(TARGET_PREFIX "${yaml_name}_${iter}")
    set(ITER_TARGET "run_iter_${TARGET_PREFIX}")

    set(SNIPPY_ELF "${ITER_SNIPPY}/snippy.elf")
    set(SNIPPY_LOG "${ITER_LOG}/snippy.log")

    set(LINKER_SCRIPT "${ITER_LINKER_DIR}/linker.ld")

    set(LINKED_ELF "${ITER_GCC}/linked.elf")
    set(GCC_LOG "${ITER_LOG}/gcc.log")

    set(ELF_LAYOUT_JSON "${ITER_ELF_LAYOUT_DIR}/elf_layout.json")
    set(ELF_LAYOUT_SVLOAD "${ITER_ELF_LAYOUT_DIR}/elf_layout.svload")
    set(ELF_LAYOUT_LOG "${ITER_LOG}/elf_layout.log")

    ibex_snippy_add_generation_command(
        YAML_FILE ${yaml_file}
        YAML_NAME ${yaml_name}
        ITER ${iter}
        SNIPPY_ELF ${SNIPPY_ELF}
        SNIPPY_LOG ${SNIPPY_LOG}
    )

    ibex_snippy_add_linker_command(
        YAML_NAME ${yaml_name}
        ITER ${iter}
        SNIPPY_ELF ${SNIPPY_ELF}
        LINKER_SCRIPT ${LINKER_SCRIPT}
    )

    ibex_snippy_add_link_command(
        YAML_NAME ${yaml_name}
        ITER ${iter}
        SNIPPY_ELF ${SNIPPY_ELF}
        LINKER_SCRIPT ${LINKER_SCRIPT}
        LINKED_ELF ${LINKED_ELF}
        GCC_LOG ${GCC_LOG}
    )

    ibex_snippy_add_elf_layout_command(
        YAML_NAME ${yaml_name}
        ITER ${iter}
        LINKED_ELF ${LINKED_ELF}
        ELF_LAYOUT_JSON ${ELF_LAYOUT_JSON}
        ELF_LAYOUT_SVLOAD ${ELF_LAYOUT_SVLOAD}
        ELF_LAYOUT_LOG ${ELF_LAYOUT_LOG}
    )

    ibex_snippy_add_cosim_target(
        TARGET_NAME ${ITER_TARGET}
        YAML_NAME ${yaml_name}
        ITER ${iter}
        ITER_DIR ${ITER_DIR}
        LINKED_ELF ${LINKED_ELF}
        ELF_LAYOUT_SVLOAD ${ELF_LAYOUT_SVLOAD}
        SNIPPY_LOG ${SNIPPY_LOG}
    )

    set(${out_var} "${ITER_TARGET}" PARENT_SCOPE)
endfunction()
