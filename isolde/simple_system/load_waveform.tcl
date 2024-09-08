# Load the VCD file


# Select the relevant signals
gtkwave::addSignalsFromList {
    clk_i
    zz_instr_i
    valid_i
    vlen_instr_o[31:0]
    internal_data
    vlen_instr_ready_o
    vlen_inst_words_o
    vlen_instr_o[63:32]
    
}


