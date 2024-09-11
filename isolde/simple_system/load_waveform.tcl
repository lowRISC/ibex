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

}


