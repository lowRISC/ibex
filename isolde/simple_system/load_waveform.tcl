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
fetch_rdata
fetch_addr
fetch_err
fetch_err_plus2
      
}


