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


module zeroriscy_mult33_hq
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic        mult_en_i,
  input  logic        operator_i,
  input  logic  [1:0] signed_mode_i,
  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,
  input  logic [31:0] alu_adder_i,
  output logic        do_sub_o,
  output logic [31:0] alu_operand_a_o,
  output logic [31:0] alu_operand_b_o,
  output logic [31:0] mult_result_o,
  output logic        carry_out_mul_o,
  output logic        ready_o
);

  logic [ 4:0] mult_state_q;
  enum logic [1:0] { MULT_IDLE, MULT_COMP, MULT_FINISH } curr_state_q;

  logic [31:0] accum_high_q, accum_low_q;
  logic [31:0] accum_high, accum_low;

  logic [33:0] res_adder_low_ext;
  logic [31:0] res_adder_low;
  logic [31:0] res_adder_high;

  logic [31:0] op_b_shift_q;
  logic [63:0] op_a_shift_q;
  logic [63:0] mult_op_a;

  logic bit_b;

  assign res_adder_high    = alu_adder_i;
  assign carry_out_mul_o   = res_adder_low_ext[33];
  assign res_adder_low     = res_adder_low_ext[32:1];
  assign res_adder_low_ext = {mult_op_a[31:0],1'b1} + {accum_low_q ^ {32{do_sub_o}}, do_sub_o};

  assign alu_operand_a_o   = mult_op_a[63:32] ^ {32{do_sub_o}};
  assign alu_operand_b_o   = accum_high_q     ^ {32{do_sub_o}};

  always_ff @(posedge clk or negedge rst_n) begin : proc_mult_state_q
    if(~rst_n) begin
      mult_state_q <= '0;
      accum_low_q  <= '0;
      accum_high_q <= '0;
      op_b_shift_q <= '0;
      op_a_shift_q <= '0;
      curr_state_q <= MULT_IDLE;
    end else begin
      if(mult_en_i) begin
            unique case(curr_state_q)
                MULT_IDLE: begin
                    op_a_shift_q <= $signed(op_a_i);
                    op_b_shift_q <= op_b_i;
                    mult_state_q <= 5'd0;
                    accum_low_q  <= '0;
                    accum_high_q <= '0;
                    curr_state_q <= MULT_COMP;
                end
                MULT_COMP: begin
                    op_a_shift_q <= op_a_shift_q << 1;
                    op_b_shift_q <= op_b_shift_q >> 1;
                    mult_state_q <= mult_state_q + 1;
                    accum_low_q  <= res_adder_low;
                    accum_high_q <= res_adder_high;
                    curr_state_q <= mult_state_q == 5'd31 ? MULT_FINISH : MULT_COMP;
                end
                MULT_FINISH: begin
                    curr_state_q <= MULT_IDLE;
                end
                default:;
            endcase // curr_state_q
       end
    end
  end

  assign do_sub_o      = op_b_shift_q[0] && mult_state_q == 5'd31 && operator_i == MUL_H;



  assign mult_op_a     = op_a_shift_q & {64{op_b_shift_q[0]}};
  assign ready_o       = curr_state_q == MULT_FINISH;
  assign mult_result_o = operator_i == MUL_H ? accum_high_q : accum_low_q;

endmodule // zeroriscy_mult
