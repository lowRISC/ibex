# Helper functions for invoking the Ibex DV Makefile.
#
# The custom Snippy CMake flow delegates RTL compile, simulation and coverage
# work to the standard Ibex DV Makefile. Keep common Make invocation details here
# so individual flow files do not duplicate:
#   - make/gmake discovery,
#   - environment variables,
#   - common metadata-sensitive arguments,
#   - common optional arguments.

find_program(IBEX_MAKE_PROGRAM NAMES gmake make REQUIRED)

# Build the environment used when invoking the Ibex DV Makefile.
#
# Usage:
#   ibex_make_env(OUT_VAR)
#
# The caller can then use:
#   COMMAND ${CMAKE_COMMAND} -E env ${OUT_VAR} ${IBEX_MAKE_PROGRAM} ...
function(ibex_make_env out_var)
    set(_env
        LOWRISC_IP_DIR=${IBEX_ROOT}/vendor/lowrisc_ip
        PRJ_DIR=${IBEX_ROOT}
        RISCV_GCC=${RISCV_GCC}
        RISCV_OBJCOPY=${RISCV_OBJCOPY}
        SPIKE_PATH=${SPIKE_PATH}
        PKG_CONFIG_PATH=${PKG_CONFIG_PATH}
    )

    set(${out_var} "${_env}" PARENT_SCOPE)
endfunction()

# Choose a stable seed for Ibex Make metadata.
#
# This is not the llvm-snippy instruction seed. llvm-snippy still auto-generates
# the real instruction seed, and run_snippy_rtl.py reads it from snippy.log.
#
# This seed is only used to keep Ibex Make metadata stable across separate CMake
# invocations.
function(ibex_make_metadata_seed out_var)
    if(SEED)
        set(_seed "${SEED}")
    elseif(COV)
        set(_seed "${SNIPPY_COV_SEED}")
    else()
        set(_seed "1")
    endif()

    set(${out_var} "${_seed}" PARENT_SCOPE)
endfunction()

# Build common Ibex Make arguments with explicit OUT and COV values.
#
# Use this for helper/preparation goals that should not share metadata with the
# main RTL simulation output directory.
#
# Usage:
#   ibex_make_common_args_for_out_with_cov(OUT_VAR "${SOME_OUT_DIR}" 0)
function(ibex_make_common_args_for_out_with_cov out_var out_dir cov_value)
    ibex_make_metadata_seed(_ibex_make_seed)

    set(_args
        OUT=${out_dir}
        SEED=${_ibex_make_seed}
        SIMULATOR=${SIMULATOR}
        ISS=${ISS}
        COV=${cov_value}
        WAVES=${WAVES}
        IBEX_CONFIG=${IBEX_CONFIG}
        TEST=${TEST}
        SIGNATURE_ADDR=${SIGNATURE_ADDR}
    )

    set(${out_var} "${_args}" PARENT_SCOPE)
endfunction()

# Build common Ibex Make arguments with an explicit COV value and the main
# Snippy/Ibex Make output directory.
#
# Usage:
#   ibex_make_common_args_with_cov(OUT_VAR 0)
function(ibex_make_common_args_with_cov out_var cov_value)
    ibex_make_common_args_for_out_with_cov(
        _args
        "${OUT}"
        "${cov_value}"
    )

    set(${out_var} "${_args}" PARENT_SCOPE)
endfunction()

# Build common Ibex Make arguments using the global COV option and the main
# Snippy/Ibex Make output directory.
#
# Usage:
#   ibex_make_common_args(OUT_VAR)
function(ibex_make_common_args out_var)
    if(COV)
        set(_ibex_make_cov 1)
    else()
        set(_ibex_make_cov 0)
    endif()

    ibex_make_common_args_with_cov(_args "${_ibex_make_cov}")
    set(${out_var} "${_args}" PARENT_SCOPE)
endfunction()

# Append RV32ZC to an existing Make argument list when configured.
#
# Usage:
#   set(MAKE_ARGS ...)
#   ibex_make_append_rv32zc_arg(MAKE_ARGS)
function(ibex_make_append_rv32zc_arg args_var)
    if(RV32ZC)
        list(APPEND ${args_var} "RV32ZC=${RV32ZC}")
        set(${args_var} "${${args_var}}" PARENT_SCOPE)
    endif()
endfunction()
