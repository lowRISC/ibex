# Load the VCD file


# Select the relevant signals
gtkwave::addSignalsFromList {
  clk_i
  rst_ni

isolde_rf_raddr_a
isolde_rf_rdata_a[127:96]
isolde_rf_rdata_a[95:64]
isolde_rf_rdata_a[63:32]
isolde_rf_rdata_a[31:0]

isolde_rf_waddr_a
isolde_rf_wdata_a[127:96]
isolde_rf_wdata_a[95:64]
isolde_rf_wdata_a[63:32]
isolde_rf_wdata_a[31:0]
isolde_rf_we_a

isolde_rf_err

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
isolde_decoder_enable_i
isolde_decoder_busy_o
isolde_decoder_illegal_instr_o

isolde_decoder_rf_waddr_a_o
isolde_decoder_rf_wdata_a_o[127:96]
isolde_decoder_rf_wdata_a_o[95:64]
isolde_decoder_rf_wdata_a_o[63:32]
isolde_decoder_rf_wdata_a_o[31:0]

isolde_decoder_rf_we_a_o

read_ptr
rd 
func7

isolde_opcode_d
isolde_opcode_q
vlen_instr_words_d
vlen_instr_words_q

isolde_decoder_instr_batch_i[6:0]
isolde_decoder_instr_batch_i[14:12]
isolde_decoder_instr_batch_i[31:25]

 fetch_exec_conn.rd
}


