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
// Design Name:    Pipelined Processor                                        //
// Module Name:    mult.sv                                                    //
// Project Name:   Processor                                                  //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Multiplier of the pipelined processor                      //
//                 Design ware multiplier requires two cycles to complete.    //
//                 Generic multiplier requires only one cycle. result will be //
//                 stored in a FF. Best synthesis results are achieved with   //
//                 moving the result register in the multiplier with automatic//
//                 retiming!                                                  //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (Oct 30th 2014) Added MAC to the multiplier                //
// Revision v0.3 - (Jan 21th 2015) Changed to a 32 bit result for             //
//                 multiplications, added vectorial support and subword       //
//                 selection. There are no flags for multiplications anymore! //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "defines.sv"

module mult
(
   input  logic [1:0]   vector_mode_i,
   input  logic [1:0]   sel_subword_i,
   input  logic [1:0]   signed_mode_i,
   input  logic         use_carry_i,
   input  logic         mac_en_i,

   input  logic [31:0]  op_a_i,
   input  logic [31:0]  op_b_i,
   input  logic [31:0]  mac_i,
   input  logic         carry_i,

   output logic [31:0]  result_o,
   output logic         carry_o,
   output logic         overflow_o
);

  logic [32:0]        result;

  logic [31:0]        op_a_sel;
  logic [31:0]        op_b_sel;
  logic [32:0]        mac_int;


  assign mac_int = (mac_en_i == 1'b1) ? mac_i : 32'b0;

  // this block performs the subword selection and sign extensions
  always_comb
  begin
    op_a_sel = op_a_i;
    op_b_sel = op_b_i;

    if(vector_mode_i == `VEC_MODE216)
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


  always_comb
  begin
    case(vector_mode_i)
      default: // VEC_MODE32, VEC_MODE216
      begin
        result[32: 0] = mac_int + op_a_sel * op_b_sel + (use_carry_i & carry_i);
      end

      `VEC_MODE16:
      begin
        result[15: 0] = op_a_sel[15: 0] * op_b_sel[15: 0];
        result[31:16] = op_a_sel[31:16] * op_b_sel[31:16];
        result[32]    = 1'b0;
      end

      `VEC_MODE8:
      begin
        result[ 7: 0] = op_a_sel[ 7: 0] * op_b_sel[ 7: 0];
        result[15: 8] = op_a_sel[15: 8] * op_b_sel[15: 8];
        result[23:16] = op_a_sel[23:16] * op_b_sel[23:16];
        result[31:24] = op_a_sel[31:24] * op_b_sel[31:24];
        result[32]    = 1'b0;
      end
    endcase; // case (vec_mode_i)
  end

  assign result_o   = result[31:0];

  assign carry_o    = result[32];

  // overflow is only used for MAC
  // If the MSB of the input MAC and the result is not the same => overflow occurred
  assign overflow_o = mac_i[31] ^ result[31];

endmodule // mult

