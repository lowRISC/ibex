# Generate a per-iteration linker script for Snippy output.
#
# Expected inputs:
#   INPUT_LD  - base linker script template
#   OUTPUT_LD - generated linker script path
#   SNIPPY_ELF - path to Snippy ELF without the trailing ".ld"
#
# The script keeps the original linker script content and replaces its last line
# with:
#   INCLUDE <SNIPPY_ELF>.ld
#
# This avoids races between parallel iterations by generating a dedicated linker
# script for each run.

if(NOT DEFINED INPUT_LD)
    message(FATAL_ERROR "INPUT_LD is not defined")
endif()

if(NOT DEFINED OUTPUT_LD)
    message(FATAL_ERROR "OUTPUT_LD is not defined")
endif()

if(NOT DEFINED SNIPPY_ELF)
    message(FATAL_ERROR "SNIPPY_ELF is not defined")
endif()

if(NOT EXISTS "${INPUT_LD}")
    message(FATAL_ERROR "Input linker script does not exist: ${INPUT_LD}")
endif()

# Ensure the output directory exists before writing the generated script.
get_filename_component(_output_dir "${OUTPUT_LD}" DIRECTORY)
file(MAKE_DIRECTORY "${_output_dir}")

file(READ "${INPUT_LD}" _ld_content)

# Normalize line endings to make the final line replacement predictable.
string(REPLACE "\r\n" "\n" _ld_content "${_ld_content}")
string(REGEX REPLACE "\n+$" "" _ld_content "${_ld_content}")

# Replace the last line with the Snippy-generated linker include.
if(_ld_content MATCHES "\n")
    string(REGEX REPLACE "\n[^\n]*$" "\nINCLUDE ${SNIPPY_ELF}.ld" _ld_content "${_ld_content}")
else()
    set(_ld_content "INCLUDE ${SNIPPY_ELF}.ld")
endif()

file(WRITE "${OUTPUT_LD}" "${_ld_content}\n")
message(STATUS "Generated linker script: ${OUTPUT_LD}")