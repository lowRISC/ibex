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


module zeroriscy_mult_slow
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic        mult_en_i,
  input  logic        operator_i,
  input  logic  [1:0] signed_mode_i,
  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,
  input  logic [33:0] alu_adder_ext_i,

  output logic [32:0] alu_operand_a_o,
  output logic [32:0] alu_operand_b_o,
  output logic [31:0] mult_result_o,

  output logic        ready_o
);

  logic [ 4:0] mult_state_q;
  enum logic [1:0] { MULT_IDLE, MULT_COMP, MULT_LASTPP, MULT_FINISH } curr_state_q;

  logic [32:0] accum_window_q;

  logic [32:0] res_adder_l;
  logic [32:0] res_adder_h;

  logic [32:0] op_b_shift_q;
  logic [32:0] op_a_shift_q;
  logic [32:0] op_a_ext, op_b_ext;
  logic [32:0] op_a_bw_pp, op_a_bw_last_pp;

  logic [31:0] b_0;

   //(accum_window_q + op_a_shift_q)
  assign res_adder_l       = alu_adder_ext_i[32:0];
   //(accum_window_q + op_a_shift_q)>>1
  assign res_adder_h       = alu_adder_ext_i[33:1];

  always_comb
  begin
    alu_operand_a_o   = accum_window_q;
    unique case(operator_i)
      MUL_L: begin
        alu_operand_b_o   = op_a_bw_pp;
      end
      MUL_H: begin
        if(curr_state_q == MULT_LASTPP)
          alu_operand_b_o   = op_a_bw_last_pp;
        else
          alu_operand_b_o   = op_a_bw_pp;
      end
    endcase
  end

  assign b_0             = {32{op_b_shift_q[0]}};

  //build the partial product
  assign op_a_bw_pp       = { ~(op_a_shift_q[32] & op_b_shift_q[0]), op_a_shift_q[31:0] & b_0 };

  assign op_a_bw_last_pp  = { op_a_shift_q[32] & op_b_shift_q[0], ~(op_a_shift_q[31:0] & b_0) };

  assign op_a_ext = {op_a_i[31] & signed_mode_i[0], op_a_i};
  assign op_b_ext = {op_b_i[31] & signed_mode_i[1], op_b_i};

  always_ff @(posedge clk or negedge rst_n) begin : proc_mult_state_q
    if(~rst_n) begin
      mult_state_q   <= '0;
      accum_window_q <= '0;
      op_b_shift_q   <= '0;
      op_a_shift_q   <= '0;
      curr_state_q   <= MULT_IDLE;
    end else begin
      if(mult_en_i) begin
            unique case(curr_state_q)
                MULT_IDLE: begin
                    op_a_shift_q   <= operator_i == MUL_H ? op_a_ext : op_a_ext << 1;
                    op_b_shift_q   <= op_b_ext >> 1;
                    mult_state_q   <= 5'd31;
                    accum_window_q <= operator_i == MUL_H ? { 1'b1, ~(op_a_ext[32] & op_b_i[0]),  op_a_ext[31:1] & {31{op_b_i[0]}}  } : {  ~(op_a_ext[32] & op_b_i[0]),  op_a_ext[31:0] & {32{op_b_i[0]}}  };
                    curr_state_q   <= MULT_COMP;
                end
                MULT_COMP: begin
                    if(operator_i == MUL_L)
                      op_a_shift_q <= op_a_shift_q << 1;
                    op_b_shift_q   <= op_b_shift_q >> 1;
                    mult_state_q   <= mult_state_q - 1;
                    accum_window_q <= operator_i == MUL_H ? res_adder_h : res_adder_l;
                    if(mult_state_q == 5'd1)
                      //if(operator_i == MUL_H)
                        curr_state_q <= MULT_LASTPP;
                      //else
                      //  curr_state_q <= MULT_FINISH;
                    else
                        curr_state_q <= MULT_COMP;
                end
                MULT_LASTPP: begin
                    accum_window_q <= res_adder_l;
                    curr_state_q   <= MULT_FINISH;
                end
                MULT_FINISH: begin
                    curr_state_q <= MULT_IDLE;
                end
                default:;
            endcase // curr_state_q
       end
    end
  end


  assign ready_o       = curr_state_q == MULT_FINISH;
  assign mult_result_o = accum_window_q;

endmodule // zeroriscy_mult
