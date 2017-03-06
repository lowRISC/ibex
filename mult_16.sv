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


module zeroriscy_mult16
#(
  parameter ADD_TYPE = 0 //0 shared
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

  enum logic [1:0] { STEP0, STEP1, STEP2 } mult_state_q, mult_state_n;
  enum logic       { MULT_00_SHIFT, MULT_16_SHIFT } shift_mul;
  logic [31:0] accum_q;

  logic [15:0] mult_op_a;
  logic [15:0] mult_op_b;
  logic [31:0] mac_op;
  logic [31:0] mult_extended;
  logic [31:0] mult_shifted;
  logic sign_a,sign_b;

  always_ff @(posedge clk or negedge rst_n) begin : proc_mult_state_q
    if(~rst_n) begin
      mult_state_q <= STEP0;
      accum_q      <= '0;
    end else begin
      if(mult_en_i) begin
        mult_state_q <= mult_state_n;
        accum_q      <= ADD_TYPE ? mult_result_o : op_acc_i;
      end
    end
  end

  always_comb
  begin : mult_fsm
      ready_o = 1'b0;
      unique case (mult_state_q)
        STEP0: begin
            //al*bl
            mult_op_a = op_a_i[15:0 ];
            mult_op_b = op_b_i[15:0 ];
            mac_op    = 32'h0;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_00_SHIFT;
            mult_state_n = STEP1;
        end
        STEP1: begin
            //al*bh<<16
            mult_op_a = op_a_i[15:0 ];
            mult_op_b = op_b_i[31:16 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = op_b_i[31];
            shift_mul = MULT_16_SHIFT;
            mult_state_n = STEP2;
        end
        STEP2: begin
            //ah*bl<<16
            mult_op_a = op_a_i[31:16];
            mult_op_b = op_b_i[15:0 ];
            mac_op    = accum_q;
            sign_a    = op_a_i[31];
            sign_b    = 1'b0;
            shift_mul = MULT_16_SHIFT;
            mult_state_n = STEP0;
            ready_o = 1'b1;
        end
        default: begin
            //al*bl
            mult_op_a = op_a_i[15:0 ];
            mult_op_b = op_b_i[15:0 ];
            mac_op    = 32'h0;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_00_SHIFT;
            mult_state_n = STEP1;
        end
      endcase // mult_state_q
  end

  assign mult_extended = $signed({sign_a,mult_op_a})*$signed({sign_b,mult_op_b});
  assign mult_result_o = ADD_TYPE ? mult_shifted + mac_op : mult_shifted;
  assign pp_acc_o      = mac_op;

  always_comb
  begin
    unique case (shift_mul)
        MULT_00_SHIFT:
            mult_shifted = mult_extended;
        MULT_16_SHIFT:
            mult_shifted = {mult_extended[15:0],16'h0};
        default:
            mult_shifted = mult_extended;
    endcase
  end

//  assign result_o      = mult_shifted + mac_op;

endmodule // zeroriscy_mult
