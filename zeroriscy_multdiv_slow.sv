// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
//                                                                            //
// Design Name:    Slow Multiplier and Division                               //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Baugh-Wooley multiplier and Long Division                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import zeroriscy_defines::*;


module zeroriscy_multdiv_slow
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic        mult_en_i,
  input  logic        div_en_i,
  input  logic  [1:0] operator_i,
  input  logic  [1:0] signed_mode_i,
  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,
  input  logic [33:0] alu_adder_ext_i,
  input  logic [31:0] alu_adder_i,
  input  logic        equal_to_zero,

  output logic [32:0] alu_operand_a_o,
  output logic [32:0] alu_operand_b_o,
  output logic [31:0] multdiv_result_o,

  output logic        ready_o
);

  logic [ 4:0] multdiv_state_q, multdiv_state_n;
  enum logic [2:0] { MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH } curr_state_q;

  logic [32:0] accum_window_q;

  logic [32:0] res_adder_l;
  logic [32:0] res_adder_h;

  logic [32:0] op_b_shift_q;
  logic [32:0] op_a_shift_q;
  logic [32:0] op_a_ext, op_b_ext;
  logic [32:0] one_shift;
  logic [32:0] op_a_bw_pp, op_a_bw_last_pp;
  logic [31:0] b_0;
  logic        sign_a, sign_b;
  logic [32:0] next_reminder, next_quotient;
  logic [32:0] op_remainder;
  logic [31:0] op_numerator_q;
  logic        is_greater_equal;
  logic        div_change_sign, rem_change_sign;


   //(accum_window_q + op_a_shift_q)
  assign res_adder_l       = alu_adder_ext_i[32:0];
   //(accum_window_q + op_a_shift_q)>>1
  assign res_adder_h       = alu_adder_ext_i[33:1];

  always_comb
  begin

    alu_operand_a_o   = accum_window_q;
    multdiv_result_o  = div_en_i ? accum_window_q[31:0] : res_adder_l;

    unique case(operator_i)

      MD_OP_MULL: begin
        alu_operand_b_o   = op_a_bw_pp;
      end

      MD_OP_MULH: begin
        if(curr_state_q == MD_LAST)
          alu_operand_b_o   = op_a_bw_last_pp;
        else
          alu_operand_b_o   = op_a_bw_pp;
      end
      default: begin
        unique case(curr_state_q)
          MD_IDLE: begin
            //0 - B = 0 iff B == 0
            alu_operand_a_o     = {32'h0  , 1'b1};
            alu_operand_b_o     = {~op_b_i, 1'b1};
          end
          MD_ABS_A: begin
            //ABS(A) = 0 - A
            alu_operand_a_o     = {32'h0  , 1'b1};
            alu_operand_b_o     = {~op_a_i, 1'b1};
          end
          MD_ABS_B: begin
            //ABS(B) = 0 - B
            alu_operand_a_o     = {32'h0  , 1'b1};
            alu_operand_b_o     = {~op_b_i, 1'b1};
          end
          MD_CHANGE_SIGN: begin
            //ABS(Quotient) = 0 - Quotient (or Reminder)
            alu_operand_a_o     = {32'h0  , 1'b1};
            alu_operand_b_o     = {~accum_window_q[31:0], 1'b1};
          end
          default: begin
            //Division
            alu_operand_a_o     = {accum_window_q[31:0], 1'b1}; //it contains the reminder
            alu_operand_b_o     = {~op_b_shift_q[31:0], 1'b1}; //denominator negated + 1 to do -denominator
          end
        endcase
      end

    endcase

  end

  /*
     The adder in the ALU computes alu_operand_a_o + alu_operand_b_o which means
     Reminder - Divisor. If Reminder - Divisor >= 0, is_greater_equal is equal to 1,
     the next Reminder is Reminder - Divisor contained in res_adder_h and the
     Quotient multdiv_state_q-th bit is set to 1 using the shift register op_b_shift_q.
     The
  */

  always_comb
  begin
    if ((accum_window_q[31] ^ op_b_shift_q[31]) == 0)
      is_greater_equal = (res_adder_h[31] == 0);
    else
      is_greater_equal = accum_window_q[31];
  end

  assign one_shift     = {32'b0, 1'b1} << multdiv_state_q;

  assign next_reminder = is_greater_equal ? res_adder_h                   : op_remainder;
  assign next_quotient = is_greater_equal ? op_a_shift_q | one_shift      : op_a_shift_q;

  assign b_0             = {32{op_b_shift_q[0]}};

  //build the partial product
  assign op_a_bw_pp       = { ~(op_a_shift_q[32] & op_b_shift_q[0]), op_a_shift_q[31:0] & b_0 };

  assign op_a_bw_last_pp  = { op_a_shift_q[32] & op_b_shift_q[0], ~(op_a_shift_q[31:0] & b_0) };

  assign sign_a   = op_a_i[31] & signed_mode_i[0];
  assign sign_b   = op_b_i[31] & signed_mode_i[1];

  assign op_a_ext = {sign_a, op_a_i};
  assign op_b_ext = {sign_b, op_b_i};

  //division
  assign op_remainder = accum_window_q[32:0];

  assign multdiv_state_n     = multdiv_state_q - 1;
  assign div_change_sign  = sign_a ^ sign_b;
  assign rem_change_sign  = sign_a;

  always_ff @(posedge clk or negedge rst_n) begin : proc_multdiv_state_q
    if(~rst_n) begin
      multdiv_state_q     <= '0;
      accum_window_q   <= '0;
      op_b_shift_q     <= '0;
      op_a_shift_q     <= '0;
      curr_state_q     <= MD_IDLE;
      op_numerator_q   <= '0;
    end else begin
      if(mult_en_i | div_en_i) begin
            unique case(curr_state_q)

                MD_IDLE: begin
                    unique case(operator_i)
                      MD_OP_MULL: begin
                        op_a_shift_q   <= op_a_ext << 1;
                        accum_window_q <= {  ~(op_a_ext[32] & op_b_i[0]),  op_a_ext[31:0] & {32{op_b_i[0]}}  };
                        op_b_shift_q   <= op_b_ext >> 1;
                        curr_state_q   <= MD_COMP;
                      end
                      MD_OP_MULH: begin
                        op_a_shift_q   <= op_a_ext;
                        accum_window_q <= { 1'b1, ~(op_a_ext[32] & op_b_i[0]),  op_a_ext[31:1] & {31{op_b_i[0]}}  };
                        op_b_shift_q   <= op_b_ext >> 1;
                        curr_state_q   <= MD_COMP;
                      end
                      MD_OP_DIV: begin
                        //Check if the Denominator is 0
                        //quotient for division by 0
                        accum_window_q <= '1;
                        curr_state_q   <= equal_to_zero ? MD_FINISH : MD_ABS_A;
                      end
                      default: begin
                        //Check if the Denominator is 0
                        //reminder for division by 0
                        accum_window_q <= op_a_ext;
                        curr_state_q   <= equal_to_zero ? MD_FINISH : MD_ABS_A;
                      end
                    endcase
                    multdiv_state_q   <= 5'd31;
                end

                MD_ABS_A: begin
                    //quotient
                    op_a_shift_q   <= '0;
                    //A abs value
                    op_numerator_q <= sign_a ? alu_adder_i : op_a_i;
                    curr_state_q   <= MD_ABS_B;
                end

                MD_ABS_B: begin
                    //reminder
                    accum_window_q   <= { 32'h0, op_numerator_q[31]};
                    //B abs value
                    op_b_shift_q     <= sign_b ? alu_adder_i : op_b_i;
                    curr_state_q     <= MD_COMP;
                end

                MD_COMP: begin

                    multdiv_state_q   <= multdiv_state_n;

                    unique case(operator_i)
                      MD_OP_MULL: begin
                        accum_window_q <= res_adder_l;
                        op_a_shift_q   <= op_a_shift_q << 1;
                        op_b_shift_q   <= op_b_shift_q >> 1;
                      end
                      MD_OP_MULH: begin
                        accum_window_q <= res_adder_h;
                        op_a_shift_q   <= op_a_shift_q;
                        op_b_shift_q   <= op_b_shift_q >> 1;
                      end
                      default: begin
                        accum_window_q <= {next_reminder[31:0], op_numerator_q[multdiv_state_n]};
                        op_a_shift_q   <= next_quotient;
                      end
                    endcase

                    if(multdiv_state_q == 5'd1)
                        curr_state_q <= MD_LAST;
                    else
                        curr_state_q <= MD_COMP;
                end

                MD_LAST: begin

                    unique case(operator_i)
                      MD_OP_MULL: begin
                        accum_window_q <= res_adder_l;
                        curr_state_q   <= MD_IDLE;
                      end
                      MD_OP_MULH: begin
                        accum_window_q <= res_adder_l;
                        curr_state_q   <= MD_IDLE;
                      end
                      MD_OP_DIV: begin
                        //this time we save the quotient in accum_window_q since we do not need anymore the reminder
                        accum_window_q <= next_quotient;
                        curr_state_q   <= MD_CHANGE_SIGN;
                      end
                      default: begin
                        //this time we do not save the quotient anymore since we need only the reminder
                        accum_window_q <= {1'b0, next_reminder[31:0]};
                        curr_state_q   <= MD_CHANGE_SIGN;
                      end
                    endcase
                end

                MD_CHANGE_SIGN: begin
                    curr_state_q   <= MD_FINISH;
                    unique case(operator_i)
                      MD_OP_DIV:
                        accum_window_q <= (div_change_sign) ? alu_adder_i : accum_window_q;
                      default:
                        accum_window_q <= (rem_change_sign) ? alu_adder_i : accum_window_q;
                    endcase
               end

                MD_FINISH: begin
                    curr_state_q <= MD_IDLE;
                end

                default:;
            endcase // curr_state_q
       end
    end
  end


  assign ready_o       = (curr_state_q == MD_FINISH) | (curr_state_q == MD_LAST & (operator_i == MD_OP_MULL | operator_i == MD_OP_MULH));


endmodule // zeroriscy_mult
