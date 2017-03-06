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
// Design Name:    Subword multiplier and MAC                                 //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Advanced MAC unit for PULP.                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import zeroriscy_defines::*;


module zeroriscy_mult32
#(
    parameter ADD_TYPE = 0, //0 shared
    parameter B_SHIFT  = 0
)
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic        mult_en_i,
//  input  logic [ 2:0] operator_i,

  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,
  input  logic [31:0] op_acc_i,

  output logic [31:0] pp_acc_o,
  output logic [31:0] mult_result_o,
  output logic        ready_o
);

  logic [ 4:0] mult_state_q;
  logic [31:0] accum_q;
  logic [31:0] op_b_shift_q, op_b_shift;
  logic [31:0] mult_op_a, mult_extended;

  logic bit_b;

  always_ff @(posedge clk or negedge rst_n) begin : proc_mult_state_q
    if(~rst_n) begin
      mult_state_q <= '0;
      accum_q      <= '0;
      op_b_shift_q <= '0;
    end else begin
      if(mult_en_i) begin
        mult_state_q <= mult_state_q + 5'h1; //rounds to 0 by itself
        accum_q      <= ADD_TYPE ? mult_result_o : op_acc_i;
        op_b_shift_q <= B_SHIFT ? op_b_shift >> 1 : '0;
      end
    end
  end

  assign ready_o       = mult_state_q == 5'd31; //(&mult_state_q)
  assign bit_b         = B_SHIFT ? op_b_shift[0] : op_b_i[mult_state_q];
  assign mult_op_a     = op_a_i & {32{bit_b}};
  assign mult_extended = mult_op_a << mult_state_q;
  assign pp_acc_o      = mult_state_q == 5'd0 ? 32'h0 : accum_q;
  assign op_b_shift    = mult_state_q == 5'd0 ? op_b_i : op_b_shift_q;
  assign mult_result_o = ADD_TYPE ? mult_extended + pp_acc_o : mult_extended;

endmodule // zeroriscy_mult
