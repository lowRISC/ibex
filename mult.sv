// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
//                                                                            //
// Design Name:    Vectorial Multiplier and MAC                               //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Advanced MAC unit for PULP.                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "riscv_defines.sv"


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
