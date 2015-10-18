////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
//                                                                            //
// Create Date:    19/09/2013                                                 //
// Design Name:    Vectorial Multiplier and MAC                               //
// Module Name:    mult.sv                                                    //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Advanced MAC unit for PULP.                                //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (Oct 30th 2014) Added MAC to the multiplier                //
// Revision v0.3 - (Jan 21th 2015) Changed to a 32 bit result for             //
//                 multiplications, added vectorial support and subword       //
//                 selection. There are no flags for multiplications anymore! //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"


module riscv_mult
(
  input  logic        mac_en_i,
  input  logic        vector_mode_i,
  input  logic [1:0]  sel_subword_i,
  input  logic [1:0]  signed_mode_i,

  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,
  input  logic [31:0] mac_i,

  output logic [31:0] result_o
);

  logic [31:0] op_a_sel;
  logic [31:0] op_b_sel;
  logic [31:0] mac_int;


  // perform subword selection and sign extensions
  always_comb
  begin
    op_a_sel = op_a_i;
    op_b_sel = op_b_i;

    if(vector_mode_i)
    begin
      if(sel_subword_i[1] == 1'b1)
        op_a_sel[15:0] = op_a_i[31:16];
      else
        op_a_sel[15:0] = op_a_i[15:0];

      if(sel_subword_i[0] == 1'b1)
        op_b_sel[15:0] = op_b_i[31:16];
      else
        op_b_sel[15:0] = op_b_i[15:0];

      op_a_sel[31:16] = {16{signed_mode_i[1] & op_a_sel[15]}};
      op_b_sel[31:16] = {16{signed_mode_i[0] & op_b_sel[15]}};
    end
  end

  assign mac_int  = (mac_en_i == 1'b1) ? mac_i : 32'b0;
  assign result_o = mac_int + op_a_sel * op_b_sel;

endmodule
