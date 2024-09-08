# Load the VCD file
#module ibex_compressed_decoder (
#  input  logic        clk_i,
#  input  logic        rst_ni,
#  input  logic        valid_i,
#  input  logic [31:0] instr_i,
#  output logic [31:0] instr_o,
#  output logic        is_compressed_o,
#  output logic        illegal_instr_o
#);

# Select the relevant signals
gtkwave::addSignalsFromList {
    clk_i
    rst_ni
    valid_i
    instr_i
    instr_o
    is_compressed_o
    illegal_instr_o
    
}


