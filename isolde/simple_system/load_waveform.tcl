# Load the VCD file


# Select the relevant signals
gtkwave::addSignalsFromList {
  clk_i
  rst_ni
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
fetch_rdata

isolde_decoder_instr_batch_i[159:128]
isolde_decoder_instr_batch_i[127:96]
isolde_decoder_instr_batch_i[95:64]
isolde_decoder_instr_batch_i[63:32]
isolde_decoder_instr_batch_i[31:0]
idvli_next
idvli_state
read_ptr
vlen_instr_words
isolde_decoder_enable_i
isolde_decoder_busy_o
isolde_decoder_illegal_instr_o
}


