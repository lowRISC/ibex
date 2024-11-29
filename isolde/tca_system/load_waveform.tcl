# Load the VCD file


# Select the relevant signals
gtkwave::addSignalsFromList {

TOP.clk_i
TOP.rst_ni
TOP.fetch_enable_i

TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.instr_addr_o[31:0]

TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.instr_rdata_i[31:0]

TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.idvli_next[2:0]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.idvli_state[2:0]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_decoder_busy_o
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_decoder_enable_i
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_decoder_illegal_instr_o

#TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_decoder_instr_batch_i[159:0]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_decoder_instr_batch_i[159:128]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_decoder_instr_batch_i[127:96]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_decoder_instr_batch_i[95:64]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_decoder_instr_batch_i[63:32]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_decoder_instr_batch_i[31:0]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_opcode_d[5:0]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.isolde_opcode_q[5:0]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.rd[4:0]

TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.read_ptr[2:0]

TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.rst_ni

TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.vlen_instr_words_d[2:0]
TOP.tb_tca_system.u_top.u_ibex_top.u_ibex_core.id_stage_i.isolde_decoder_i.vlen_instr_words_q[2:0]

TOP.tb_tca_system.core_xif.issue_valid
TOP.tb_tca_system.core_xif.issue_ready
TOP.tb_tca_system.core_xif.issue_req[149:118]
TOP.tb_tca_system.core_xif.issue_req[105:74]
TOP.tb_tca_system.core_xif.issue_req[73:42]
TOP.tb_tca_system.core_xif.issue_req[41:10]
TOP.tb_tca_system.core_xif.issue_req[9:7]


}


