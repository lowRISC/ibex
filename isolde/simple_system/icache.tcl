

# Select the relevant signals
gtkwave::addSignalsFromList {
  clk_i
  rst_ni
  req_i
  branch_i
  addr_i
  ready_i
  valid_o
  rdata_o
  addr_o
  err_o
  err_plus2_o
  instr_req_o
  instr_gnt_i
  instr_addr_o
  instr_rdata_i
  instr_err_i
  instr_rvalid_i   
   fetch_ready         
   fetch_valid_raw     
    fetch_rdata         
    fetch_addr          
     fetch_err           
     fetch_err_plus2      
}


