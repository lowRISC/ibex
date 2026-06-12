# Generate the riscv-dv assembly input used by the Snippy flow.
#
# This file performs two steps:
#   1. generate the Ibex riscv-dv core settings file,
#   2. run riscv-dv in generation mode to produce the assembly test.
#
# Why core_config uses a separate OUT directory:
#
# The Ibex Makefile stores a metadata context under OUT/metadata. That metadata
# is tied to the particular Make invocation and to metadata-sensitive variables
# such as COV, SIMULATOR, ISS, TEST, SEED, SIGNATURE_ADDR and IBEX_CONFIG.
#
# In this CMake flow, GOAL=core_config is only a preparation step. It generates
# riscv_core_setting.sv so that riscv-dv can produce the bootstrap assembly used
# later when linking the Snippy payload.
#
# The main Ibex OUT directory, OUT, is reserved for the actual RTL
# compile, Snippy RTL simulations and coverage collection. If core_config writes
# metadata into the same OUT directory, the later rtl_tb_compile invocation may
# observe a mismatched metadata context and rebuild/reconfigure the instruction
# generator unexpectedly.
#
# Therefore core_config intentionally uses a separate temporary OUT directory:
#
#   build/ibex_core_config_out
#
# while the main flow uses:
#
#   build/ibex_make_out
#
# This keeps the riscv-dv preparation metadata isolated from the real simulation
# metadata.

# Keep riscv-dv/core-config logs next to other riscv-dv generated artifacts.
set(DIR_DV_LOG "${DIR_DV}/log")
file(MAKE_DIRECTORY "${DIR_DV_LOG}")

# Generate riscv_core_setting.sv required by the Ibex riscv-dv flow.
set(RISCV_CORE_SETTING "${CORE_IBEX_ROOT}/riscv_dv_extension/riscv_core_setting.sv")
set(CORE_CONFIG_LOG "${DIR_DV_LOG}/core_config.log")

# Separate metadata sandbox for the preparation-only core_config Make goal.
# Do not replace this with OUT unless core_config is integrated into
# the main Ibex Make flow without creating a separate metadata context.
set(IBEX_CORE_CONFIG_OUT "${CMAKE_BINARY_DIR}/ibex_core_config_out")

ibex_make_env(IBEX_MAKE_ENV)
ibex_make_common_args_for_out_with_cov(
    IBEX_CORE_CONFIG_COMMON_ARGS
    "${IBEX_CORE_CONFIG_OUT}"
    0
)

set(IBEX_CORE_CONFIG_MAKE_ARGS
    -B
    run
    GOAL=core_config
    ${IBEX_CORE_CONFIG_COMMON_ARGS}
)

ibex_make_append_rv32zc_arg(IBEX_CORE_CONFIG_MAKE_ARGS)

add_custom_command(
    OUTPUT ${RISCV_CORE_SETTING}
    COMMAND ${CMAKE_COMMAND} -E make_directory "${DIR_DV_LOG}" "${IBEX_CORE_CONFIG_OUT}"
    COMMAND ${CMAKE_COMMAND} -E env
            ${IBEX_MAKE_ENV}
            ${IBEX_MAKE_PROGRAM}
            ${IBEX_CORE_CONFIG_MAKE_ARGS}
            > "${CORE_CONFIG_LOG}" 2>&1
    COMMAND test -f "${RISCV_CORE_SETTING}"
    WORKING_DIRECTORY "${CORE_IBEX_ROOT}"
    COMMENT "Config core → ${RISCV_CORE_SETTING}"
    VERBATIM
)

# Run riscv-dv in generation mode and produce one assembly program.
set(DV_ASM "${DIR_DV}/generated_asm")
set(GEN_ASM "${DV_ASM}/asm_test/${TEST}_0.S")
set(RISCV_DV_RUN_PY "${IBEX_ROOT}/vendor/google_riscv-dv/run.py")
set(RISCV_DV_GEN_LOG "${DIR_DV_LOG}/gen.log")

# Common riscv-dv generation settings used by this flow.
set(RISCV_DV_MABI "ilp32")
set(RISCV_DV_SIGNATURE_ADDR "${SIGNATURE_ADDR}")
set(RISCV_DV_STEPS "gen")
set(RISCV_DV_GEN_ITERATIONS 1)

# UVM overrides and Ibex-specific runtime options passed into riscv-dv.
set(RISCV_DV_SIM_OPTS
    "+uvm_set_inst_override=riscv_asm_program_gen,ibex_asm_program_gen,uvm_test_top.asm_gen \
+uvm_set_type_override=riscv_instr_sequence,snippy_func_instr,1 \
+uvm_set_inst_override=ibex_asm_program_gen,snippy_asm_program_gen,uvm_test_top.asm_gen \
+uvm_set_type_override=riscv_instr_gen_config,ibex_riscv_instr_gen_config,1 \
+boot_mode=m \
+require_signature_addr=1 \
+signature_addr=${RISCV_DV_SIGNATURE_ADDR} \
+pmp_num_regions=16 \
+pmp_granularity=0 \
+tvec_alignment=8 \
+fix_sp=1"
)

# Full argument list for run.py.
set(RISCV_DV_COMMON_ARGS
    --testlist ${TESTLIST}
    --custom_target ${CUSTOM_TARGET}
    --csr_yaml ${CSR_YAML}
    --test ${TEST}
    --isa ${TOOLCHAIN_ISA}
    --sim_opts "${RISCV_DV_SIM_OPTS}"
    --mabi ${RISCV_DV_MABI}
    --steps=${RISCV_DV_STEPS}
    --end_signature_addr ${RISCV_DV_SIGNATURE_ADDR}
    --iterations ${RISCV_DV_GEN_ITERATIONS}
    --o ${DV_ASM}
)

add_custom_command(
    OUTPUT ${GEN_ASM}
    COMMAND ${CMAKE_COMMAND} -E make_directory "${DIR_DV_LOG}"
    COMMAND python3 ${RISCV_DV_RUN_PY}
            ${RISCV_DV_COMMON_ARGS}
            > "${RISCV_DV_GEN_LOG}" 2>&1
    DEPENDS
            ${RISCV_CORE_SETTING}
            ${TESTLIST}
            ${CSR_YAML}
    WORKING_DIRECTORY ${DIR_DV}
    COMMENT "Generating test assembly with riscv-dv → ${GEN_ASM}"
    VERBATIM
)

# User-facing target for building the generated assembly input.
add_custom_target(build_riscv_dv
    DEPENDS ${GEN_ASM}
    COMMENT "Build riscv-dv generated assembly"
)
