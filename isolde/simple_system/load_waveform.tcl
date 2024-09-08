# Load the VCD file


# Select the relevant signals
gtkwave::addSignalsFromList {
  clk_i
  rst_ni
  vlen_instr_req_i          //request for next instruction
  word_instr_ready_i               // Signals that word_instr_i can be used
  word_instr_i               // Instruction input from icache
  word_instr_req_o               // request a word_instr_i
  vlen_instr_o     // In-order succession of maximum 5 word_instr_i
  vlen_instr_words_o     // Instruction length in words
  vlen_instr_ready_o   

fetch_req
fetch_valid_raw
fetch_rdata
fetch_addr
fetch_addr
fetch_err
fetch_err_plus2
      
}


