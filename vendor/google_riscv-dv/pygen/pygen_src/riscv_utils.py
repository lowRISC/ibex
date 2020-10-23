"""
Copyright 2020 Google LLC
Copyright 2020 PerfectVIPs Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.

"""
import sys
import logging
import pandas as pd
from tabulate import tabulate
from pygen_src.isa import rv32i_instr
from pygen_src.isa import rv32m_instr
from pygen_src.isa import rv32c_instr
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_directed_instr_lib import (riscv_directed_instr_stream,
                                                riscv_int_numeric_corner_stream,
                                                riscv_jal_instr)


def factory(obj_of):
    objs = {
        "riscv_directed_instr_stream": riscv_directed_instr_stream,
        "riscv_int_numeric_corner_stream": riscv_int_numeric_corner_stream,
        "riscv_jal_instr": riscv_jal_instr
    }

    try:
        return objs[obj_of]()
    except KeyError:
        logging.critical("Cannot Create object of %s", obj_of)
        sys.exit(1)


def get_object(instr):
    try:
        instr_inst = eval("rv32i_instr.riscv_" + instr.name + "_instr()")
    except Exception:
        try:
            instr_inst = eval("rv32m_instr.riscv_" + instr.name + "_instr()")
        except Exception:
            try:
                instr_inst = eval("rv32c_instr.riscv_" + instr.name + "_instr()")
            except Exception:
                logging.critical("Failed to create instr: %0s", instr.name)
                sys.exit(1)
    return instr_inst


def gen_config_table():
    data = []
    data.append(['main_program_instr_cnt', type(cfg.main_program_instr_cnt),
                 sys.getsizeof(cfg.main_program_instr_cnt), cfg.main_program_instr_cnt])
    data.append(['sub_program_instr_cnt', type(cfg.sub_program_instr_cnt),
                 sys.getsizeof(cfg.sub_program_instr_cnt), cfg.sub_program_instr_cnt])
    data.append(['debug_program_instr_cnt', type(cfg.debug_program_instr_cnt),
                 sys.getsizeof(cfg.debug_program_instr_cnt), cfg.debug_program_instr_cnt])
    data.append(['debug_sub_program_instr_cnt', type(cfg.debug_sub_program_instr_cnt),
                 sys.getsizeof(cfg.debug_sub_program_instr_cnt),
                 cfg.debug_sub_program_instr_cnt])
    data.append(['max_directed_instr_stream_seq', type(cfg.max_directed_instr_stream_seq),
                 sys.getsizeof(cfg.max_directed_instr_stream_seq),
                 cfg.max_directed_instr_stream_seq])
    data.append(['data_page_pattern', type(cfg.data_page_pattern),
                 sys.getsizeof(cfg.data_page_pattern), cfg.data_page_pattern])
    data.append(['init_privileged_mode', type(cfg.init_privileged_mode),
                 sys.getsizeof(cfg.init_privileged_mode), cfg.init_privileged_mode])
    data.append(['scratch_reg', type(cfg.scratch_reg),
                 sys.getsizeof(cfg.scratch_reg), cfg.scratch_reg])
    data.append(['pmp_reg', type(cfg.pmp_reg), sys.getsizeof(cfg.pmp_reg), cfg.pmp_reg])
    data.append(['reserved_regs', type(cfg.reserved_regs),
                 sys.getsizeof(cfg.reserved_regs), cfg.reserved_regs])
    data.append(['sp', type(cfg.sp), sys.getsizeof(cfg.sp), cfg.sp])
    data.append(['tp', type(cfg.tp), sys.getsizeof(cfg.tp), cfg.tp])
    data.append(['ra', type(cfg.ra), sys.getsizeof(cfg.ra), cfg.ra])
    data.append(['check_misa_init_val', type(cfg.check_misa_init_val),
                 sys.getsizeof(cfg.check_misa_init_val), cfg.check_misa_init_val])
    data.append(['check_xstatus', type(cfg.check_xstatus),
                 sys.getsizeof(cfg.check_xstatus), cfg.check_xstatus])
    data.append(['virtual_addr_translation_on', type(cfg.virtual_addr_translation_on),
                 sys.getsizeof(cfg.virtual_addr_translation_on),
                 cfg.virtual_addr_translation_on])
    data.append(['kernel_stack_len', type(cfg.kernel_stack_len),
                 sys.getsizeof(cfg.kernel_stack_len), cfg.kernel_stack_len])
    data.append(['kernel_program_instr_cnt', type(cfg.kernel_program_instr_cnt),
                 sys.getsizeof(cfg.kernel_program_instr_cnt), cfg.kernel_program_instr_cnt])
    data.append(['num_of_sub_program', type(cfg.num_of_sub_program),
                 sys.getsizeof(cfg.num_of_sub_program), cfg.num_of_sub_program])
    data.append(['instr_cnt', type(cfg.instr_cnt), sys.getsizeof(cfg.instr_cnt), cfg.instr_cnt])
    data.append(['num_of_tests', type(cfg.num_of_tests),
                 sys.getsizeof(cfg.num_of_tests), cfg.num_of_tests])
    data.append(['no_data_page', type(cfg.no_data_page),
                 sys.getsizeof(cfg.no_data_page), cfg.no_data_page])
    data.append(['no_branch_jump', type(cfg.no_branch_jump),
                 sys.getsizeof(cfg.no_branch_jump), cfg.no_branch_jump])
    data.append(['no_load_store', type(cfg.no_load_store),
                 sys.getsizeof(cfg.no_load_store), cfg.no_load_store])
    data.append(['no_csr_instr', type(cfg.no_csr_instr),
                 sys.getsizeof(cfg.no_csr_instr), cfg.no_csr_instr])
    data.append(['no_ebreak', type(cfg.no_ebreak), sys.getsizeof(cfg.no_ebreak), cfg.no_ebreak])
    data.append(['no_dret', type(cfg.no_dret), sys.getsizeof(cfg.no_dret), cfg.no_dret])
    data.append(['no_fence', type(cfg.no_fence), sys.getsizeof(cfg.no_fence), cfg.no_fence])
    data.append(['no_wfi', type(cfg.no_wfi), sys.getsizeof(cfg.no_wfi), cfg.no_wfi])
    data.append(['enable_unaligned_load_store', type(cfg.enable_unaligned_load_store),
                 sys.getsizeof(cfg.enable_unaligned_load_store),
                 cfg.enable_unaligned_load_store])
    data.append(['illegal_instr_ratio', type(cfg.illegal_instr_ratio),
                 sys.getsizeof(cfg.illegal_instr_ratio), cfg.illegal_instr_ratio])
    data.append(['hint_instr_ratio', type(cfg.hint_instr_ratio),
                 sys.getsizeof(cfg.hint_instr_ratio), cfg.hint_instr_ratio])
    data.append(['num_of_harts', type(cfg.num_of_harts),
                 sys.getsizeof(cfg.num_of_harts), cfg.num_of_harts])
    data.append(['fix_sp', type(cfg.fix_sp), sys.getsizeof(cfg.fix_sp), cfg.fix_sp])
    data.append(['use_push_data_section', type(cfg.use_push_data_section),
                 sys.getsizeof(cfg.use_push_data_section), cfg.use_push_data_section])
    data.append(['boot_mode_opts', type(cfg.boot_mode_opts),
                 sys.getsizeof(cfg.boot_mode_opts), cfg.boot_mode_opts])
    data.append(['enable_page_table_exception', type(cfg.enable_page_table_exception),
                 sys.getsizeof(cfg.enable_page_table_exception),
                 cfg.enable_page_table_exception])
    data.append(['no_directed_instr', type(cfg.no_directed_instr),
                 sys.getsizeof(cfg.no_directed_instr), cfg.no_directed_instr])
    data.append(['asm_test_suffix', type(cfg.asm_test_suffix),
                 sys.getsizeof(cfg.asm_test_suffix), cfg.asm_test_suffix])
    data.append(['enable_interrupt', type(cfg.enable_interrupt),
                 sys.getsizeof(cfg.enable_interrupt), cfg.enable_interrupt])
    data.append(['enable_nested_interrupt', type(cfg.enable_nested_interrupt),
                 sys.getsizeof(cfg.enable_nested_interrupt), cfg.enable_nested_interrupt])
    data.append(['enable_timer_irq', type(cfg.enable_timer_irq),
                 sys.getsizeof(cfg.enable_timer_irq), cfg.enable_timer_irq])
    data.append(['bare_program_mode', type(cfg.bare_program_mode),
                 sys.getsizeof(cfg.bare_program_mode), cfg.bare_program_mode])
    data.append(['enable_illegal_csr_instruction', type(cfg.enable_illegal_csr_instruction),
                 sys.getsizeof(cfg.enable_illegal_csr_instruction),
                 cfg.enable_illegal_csr_instruction])
    data.append(['enable_access_invalid_csr_level', type(cfg.enable_access_invalid_csr_level),
                 sys.getsizeof(cfg.enable_access_invalid_csr_level),
                 cfg.enable_access_invalid_csr_level])
    data.append(['enable_misaligned_instr', type(cfg.enable_misaligned_instr),
                 sys.getsizeof(cfg.enable_misaligned_instr), cfg.enable_misaligned_instr])
    data.append(['enable_dummy_csr_write', type(cfg.enable_dummy_csr_write),
                 sys.getsizeof(cfg.enable_dummy_csr_write), cfg.enable_dummy_csr_write])
    data.append(['randomize_csr', type(cfg.randomize_csr),
                 sys.getsizeof(cfg.randomize_csr), cfg.randomize_csr])
    data.append(['allow_sfence_exception', type(cfg.allow_sfence_exception),
                 sys.getsizeof(cfg.allow_sfence_exception), cfg.allow_sfence_exception])
    data.append(['no_delegation', type(cfg.no_delegation),
                 sys.getsizeof(cfg.no_delegation), cfg.no_delegation])
    data.append(['force_m_delegation', type(cfg.force_m_delegation),
                 sys.getsizeof(cfg.force_m_delegation), cfg.force_m_delegation])
    data.append(['force_s_delegation', type(cfg.force_s_delegation),
                 sys.getsizeof(cfg.force_s_delegation), cfg.force_s_delegation])
    data.append(['support_supervisor_mode', type(cfg.support_supervisor_mode),
                 sys.getsizeof(cfg.support_supervisor_mode), cfg.support_supervisor_mode])
    data.append(['disable_compressed_instr', type(cfg.disable_compressed_instr),
                 sys.getsizeof(cfg.disable_compressed_instr), cfg.disable_compressed_instr])
    data.append(['require_signature_addr', type(cfg.require_signature_addr),
                 sys.getsizeof(cfg.require_signature_addr), cfg.require_signature_addr])
    data.append(['signature_addr', type(cfg.signature_addr),
                 sys.getsizeof(cfg.signature_addr), cfg.signature_addr])
    data.append(['gen_debug_section', type(cfg.gen_debug_section),
                 sys.getsizeof(cfg.gen_debug_section), cfg.force_s_delegation])
    data.append(['enable_ebreak_in_debug_rom', type(cfg.enable_ebreak_in_debug_rom),
                 sys.getsizeof(cfg.enable_ebreak_in_debug_rom), cfg.enable_ebreak_in_debug_rom])
    data.append(['set_dcsr_ebreak', type(cfg.set_dcsr_ebreak),
                 sys.getsizeof(cfg.set_dcsr_ebreak), cfg.set_dcsr_ebreak])
    data.append(['num_debug_sub_program', type(cfg.num_debug_sub_program),
                 sys.getsizeof(cfg.num_debug_sub_program), cfg.num_debug_sub_program])
    data.append(['enable_debug_single_step', type(cfg.enable_debug_single_step),
                 sys.getsizeof(cfg.enable_debug_single_step), cfg.enable_debug_single_step])
    data.append(['single_step_iterations', type(cfg.single_step_iterations),
                 sys.getsizeof(cfg.single_step_iterations), cfg.single_step_iterations])
    data.append(['set_mstatus_tw', type(cfg.set_mstatus_tw),
                 sys.getsizeof(cfg.set_mstatus_tw), cfg.set_mstatus_tw])
    data.append(['set_mstatus_mprv', type(cfg.set_mstatus_mprv),
                 sys.getsizeof(cfg.set_mstatus_mprv), cfg.set_mstatus_mprv])
    data.append(['enable_floating_point', type(cfg.enable_floating_point),
                 sys.getsizeof(cfg.enable_floating_point), cfg.enable_floating_point])
    data.append(['enable_vector_extension', type(cfg.enable_vector_extension),
                 sys.getsizeof(cfg.enable_vector_extension), cfg.enable_vector_extension])
    data.append(['enable_b_extension', type(cfg.enable_b_extension),
                 sys.getsizeof(cfg.enable_b_extension), cfg.enable_b_extension])

    df = pd.DataFrame(data, columns=['Name', 'Type', 'Size', 'Value'])
    df['Value'] = df['Value'].apply(str)
    logging.info('\n' + tabulate(df, headers='keys', tablefmt='psql'))
