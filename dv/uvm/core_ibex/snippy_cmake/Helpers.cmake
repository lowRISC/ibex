# Helper functions shared across the custom Snippy flow.
#
# These helpers keep the main CMake files smaller and encapsulate:
#   - YAML file resolution and filtering,
#   - per-iteration directory layout creation,
#   - gcc link command construction.

# Resolve one YAML file name provided via SNIPPY_TEST.
#
# Supported forms:
#   name
#   name.yaml
#   layout_name.yaml
function(ibex_snippy_resolve_yaml_file yaml_dir filter_item out_var)
    set(_found_file "")

    if(EXISTS "${yaml_dir}/${filter_item}")
        set(_found_file "${yaml_dir}/${filter_item}")
    elseif(EXISTS "${yaml_dir}/${filter_item}.yaml")
        set(_found_file "${yaml_dir}/${filter_item}.yaml")
    elseif(EXISTS "${yaml_dir}/layout_${filter_item}.yaml")
        set(_found_file "${yaml_dir}/layout_${filter_item}.yaml")
    endif()

    set(${out_var} "${_found_file}" PARENT_SCOPE)
endfunction()

# Build the final list of YAML inputs selected by SNIPPY_TEST.
#
# Only files matching layout_*.yaml are accepted into the flow.
function(ibex_snippy_select_yaml_files yaml_dir yaml_filter out_var)
    set(_yaml_files "")

    string(REPLACE "," ";" _filter_list "${yaml_filter}")

    foreach(_filter_item ${_filter_list})
        string(STRIP "${_filter_item}" _filter_item_clean)

        ibex_snippy_resolve_yaml_file("${yaml_dir}" "${_filter_item_clean}" _found_file)

        if(_found_file)
            get_filename_component(_filename "${_found_file}" NAME)
            if(_filename MATCHES "^layout_.*\\.yaml$")
                list(APPEND _yaml_files "${_found_file}")
                message(STATUS "Added YAML file from filter: ${_filename}")
            else()
                message(WARNING "File ${_filename} does not match pattern 'layout_*.yaml' and will be ignored")
            endif()
        else()
            message(WARNING "Requested YAML file '${_filter_item_clean}' not found in ${yaml_dir}")
        endif()
    endforeach()

    list(REMOVE_DUPLICATES _yaml_files)
    set(${out_var} "${_yaml_files}" PARENT_SCOPE)
endfunction()

# Create the standard per-iteration directory layout and export the paths to the
# caller scope.
function(ibex_snippy_init_iteration_layout yaml_base_dir yaml_name iter)
    set(_iter_dir "${yaml_base_dir}/${yaml_name}_${iter}")

    set(_iter_snippy "${_iter_dir}/snippy")
    set(_iter_log "${_iter_dir}/log")
    set(_iter_gcc "${_iter_dir}/gcc")
    set(_iter_linker_dir "${_iter_dir}/linker")
    set(_iter_elf_layout_dir "${_iter_dir}/elf_layout")

    file(MAKE_DIRECTORY
        ${_iter_dir}
        ${_iter_snippy}
        ${_iter_log}
        ${_iter_gcc}
        ${_iter_linker_dir}
        ${_iter_elf_layout_dir}
    )

    set(ITER_DIR "${_iter_dir}" PARENT_SCOPE)
    set(ITER_SNIPPY "${_iter_snippy}" PARENT_SCOPE)
    set(ITER_LOG "${_iter_log}" PARENT_SCOPE)
    set(ITER_GCC "${_iter_gcc}" PARENT_SCOPE)
    set(ITER_LINKER_DIR "${_iter_linker_dir}" PARENT_SCOPE)
    set(ITER_ELF_LAYOUT_DIR "${_iter_elf_layout_dir}" PARENT_SCOPE)
endfunction()

# Add one gcc link command for a generated test iteration.
#
# The command expects:
#   - output ELF path,
#   - log path,
#   - linker script,
#   - gcc arguments,
#   - input objects/files,
#   - build dependencies.
function(ibex_snippy_add_gcc_link_command)
    set(options)
    set(oneValueArgs
        OUTPUT
        LOG
        LINKER_SCRIPT
        COMMENT
    )
    set(multiValueArgs
        INPUTS
        DEPENDS
        GCC_ARGS
    )

    cmake_parse_arguments(GCC_LINK "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

    if(NOT GCC_LINK_OUTPUT)
        message(FATAL_ERROR "ibex_snippy_add_gcc_link_command: OUTPUT is required")
    endif()

    if(NOT GCC_LINK_LOG)
        message(FATAL_ERROR "ibex_snippy_add_gcc_link_command: LOG is required")
    endif()

    if(NOT GCC_LINK_LINKER_SCRIPT)
        message(FATAL_ERROR "ibex_snippy_add_gcc_link_command: LINKER_SCRIPT is required")
    endif()

    if(NOT GCC_LINK_GCC_ARGS)
        message(FATAL_ERROR "ibex_snippy_add_gcc_link_command: GCC_ARGS is required")
    endif()

    add_custom_command(
        OUTPUT ${GCC_LINK_OUTPUT}
        BYPRODUCTS ${GCC_LINK_LOG}
        COMMAND ${RISCV_GCC}
                ${GCC_LINK_GCC_ARGS}
                ${GCC_LINK_INPUTS}
                -T ${GCC_LINK_LINKER_SCRIPT}
                -o ${GCC_LINK_OUTPUT}
                &> ${GCC_LINK_LOG}
        DEPENDS ${GCC_LINK_DEPENDS}
        COMMENT "${GCC_LINK_COMMENT}"
        VERBATIM
    )
endfunction()
