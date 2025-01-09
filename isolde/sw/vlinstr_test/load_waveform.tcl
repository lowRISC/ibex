# Select the relevant signals
gtkwave::addSignalsFromList {
  clk_i
  rst_ni

  i_dummy_imemory.tcdm[0].req
  i_dummy_imemory.tcdm[0].gnt
  i_dummy_imemory.tcdm[0].r_valid
  i_dummy_imemory.tcdm[0].add[31:0]
  i_dummy_imemory.tcdm[0].r_data[31:0]

  vlen_instr_req_i          
  vlen_instr_o[31:0]
  word_instr_req_o 
  word_instr_ready_i
  vlen_instr_ready_o
  ifvli_state                 
  word_instr_i                                   
  vlen_instr_words_o     
     
fetch_req
fetch_valid_raw
vlen_instr_o[31:0]
fetch_rdata
fetch_addr
fetch_err
fetch_err_plus2

vlen_instr_o[159:128]
vlen_instr_o[127:96]
vlen_instr_o[95:64]
vlen_instr_o[63:32]
vlen_instr_o[31:0]
u_top.u_ibex_top.u_ibex_core.if_stage_i.fetch_rdata[31:0]

u_top.u_ibex_top.u_ibex_core.instr_valid_id
u_top.u_ibex_top.u_ibex_core.instr_batch_rdata_id[159:128]
u_top.u_ibex_top.u_ibex_core.instr_batch_rdata_id[127:96]
u_top.u_ibex_top.u_ibex_core.instr_batch_rdata_id[95:64]
u_top.u_ibex_top.u_ibex_core.instr_batch_rdata_id[63:32]
u_top.u_ibex_top.u_ibex_core.instr_batch_rdata_id[31:0]
u_top.u_ibex_top.u_ibex_core.instr_rdata_id[31:0]

clk_i
isolde_decoder_instr_valid_i
isolde_decoder_instr_batch_i[159:128]
isolde_decoder_instr_batch_i[127:96]
isolde_decoder_instr_batch_i[95:64]
isolde_decoder_instr_batch_i[63:32]
isolde_decoder_instr_batch_i[31:0]

idvli_next
idvli_state
read_ptr
instr_rdata_std
instr_rdata_alu_std
isolde_decoder_busy_o
isolde_decoder_illegal_instr_o

isolde_opcode_d
isolde_opcode_q

vlen_instr_words_d
vlen_instr_words_q
}