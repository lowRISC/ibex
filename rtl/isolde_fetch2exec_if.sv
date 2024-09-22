// Copyleft 2024

interface isolde_fetch2exec_if (
    input logic clk_i
);
  logic isolde_decoder_enable;  // custom instr is decoded
  logic isolde_decoder_illegal_instr;  // unsupported custom instr encountered
  logic isolde_decoder_ready;  //decoder busy
  //
  isolde_decoder_pkg::isolde_opcode_e isolde_opcode;  //decoded instruction
  logic [2:0] func3;  //instr[14-12]
  logic [4:0] rd;  //register destination vector
  logic [4:0] rs1;  //register source vector 
  logic [4:0] rs2;  //register source vector 

endinterface
