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
// Design Name:    Fast Multiplier and Division                               //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    16x16 kernel multiplier and Long Division                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import zeroriscy_defines::*;

`define OP_L 15:0
`define OP_H 31:16

module zeroriscy_multdiv_fast
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

  logic [ 4:0] div_counter_q, div_counter_n;
  enum logic [1:0] {ALBL, ALBH, AHBL, AHBH } mult_state_q, mult_state_n;
  enum logic [2:0] { MD_IDLE, MD_ABS_A, MD_ABS_B, MD_COMP, MD_LAST, MD_CHANGE_SIGN, MD_FINISH } divcurr_state_q, divcurr_state_n;

  logic [34:0] mac_res_ext;
  logic [33:0] mac_res_q, mac_res_n, mac_res, op_reminder_n;
  logic [15:0] mult_op_a;
  logic [15:0] mult_op_b;
  logic [33:0] accum;
  logic        sign_a, sign_b;
  logic        div_sign_a, div_sign_b;
  logic        signed_mult;
  logic        is_greater_equal;
  logic        div_change_sign, rem_change_sign;
  logic [31:0] one_shift;
  logic [31:0] op_denominator_q;
  logic [31:0] op_numerator_q;
  logic [31:0] op_quotient_q;
  logic [31:0] op_denominator_n;
  logic [31:0] op_numerator_n;
  logic [31:0] op_quotient_n;
  logic [32:0] next_reminder, next_quotient;
  logic [32:0] res_adder_h;
  logic        mult_is_ready;

  always_ff @(posedge clk or negedge rst_n) begin : proc_mult_state_q
    if(~rst_n) begin
      mult_state_q      <= ALBL;
      mac_res_q         <= '0;
      div_counter_q     <= '0;
      divcurr_state_q   <= MD_IDLE;
      op_denominator_q  <= '0;
      op_numerator_q    <= '0;
      op_quotient_q     <= '0;
    end else begin

      if(mult_en_i) begin
        mult_state_q <= mult_state_n;
      end

      if(div_en_i) begin
        div_counter_q     <= div_counter_n;
        op_denominator_q  <= op_denominator_n  ;
        op_numerator_q    <= op_numerator_n    ;
        op_quotient_q     <= op_quotient_n     ;
        divcurr_state_q   <= divcurr_state_n;
      end

      unique case(1'b1)
        mult_en_i:
          mac_res_q <= mac_res_n;
        div_en_i:
          mac_res_q <= op_reminder_n;
        default:
          mac_res_q <= mac_res_q;
       endcase

    end
  end

  assign signed_mult    = (signed_mode_i != 2'b00);

  assign multdiv_result_o = div_en_i ? mac_res_q[31:0] : mac_res_n[31:0];

  assign mac_res_ext = $signed({sign_a, mult_op_a})*$signed({sign_b, mult_op_b}) + $signed(accum);
  assign mac_res     = mac_res_ext[33:0];

  assign res_adder_h   = alu_adder_ext_i[33:1];

  assign next_reminder = is_greater_equal ? res_adder_h                   : mac_res_q[32:0];
  assign next_quotient = is_greater_equal ? op_quotient_q | one_shift     : op_quotient_q;

  assign one_shift     = {31'b0, 1'b1} << div_counter_q;

  /*
     The adder in the ALU computes alu_operand_a_o + alu_operand_b_o which means
     Reminder - Divisor. If Reminder - Divisor >= 0, is_greater_equal is equal to 1,
     the next Reminder is Reminder - Divisor contained in res_adder_h and the
  */

  always_comb
  begin
    if ((mac_res_q[31] ^ op_denominator_q[31]) == 0)
      is_greater_equal = (res_adder_h[31] == 0);
    else
      is_greater_equal = mac_res_q[31];
  end

  assign div_sign_a   = op_a_i[31] & signed_mode_i[0];
  assign div_sign_b   = op_b_i[31] & signed_mode_i[1];
  assign div_change_sign  = div_sign_a ^ div_sign_b;
  assign rem_change_sign  = div_sign_a;


  always_comb
  begin : div_fsm
      div_counter_n    = div_counter_q - 1;
      op_reminder_n    = mac_res_q;
      op_quotient_n    = op_quotient_q;
      divcurr_state_n  = divcurr_state_q;
      op_numerator_n   = op_numerator_q;
      op_denominator_n = op_denominator_q;
      alu_operand_a_o  = {32'h0  , 1'b1};
      alu_operand_b_o  = {~op_b_i, 1'b1};

      unique case(divcurr_state_q)
          MD_IDLE: begin
              unique case(operator_i)
                MD_OP_DIV: begin
                  //Check if the Denominator is 0
                  //quotient for division by 0
                  op_reminder_n    = '1;
                  divcurr_state_n  = equal_to_zero ? MD_FINISH : MD_ABS_A;
                end
                default: begin
                  //Check if the Denominator is 0
                  //reminder for division by 0
                  op_reminder_n     = {2'b0, op_a_i};
                  divcurr_state_n    = equal_to_zero ? MD_FINISH : MD_ABS_A;
                end
              endcase
              //0 - B = 0 iff B == 0
              alu_operand_a_o     = {32'h0  , 1'b1};
              alu_operand_b_o     = {~op_b_i, 1'b1};
              div_counter_n        = 5'd31;
          end

          MD_ABS_A: begin
              //quotient
              op_quotient_n  = '0;
              //A abs value
              op_numerator_n = div_sign_a ? alu_adder_i : op_a_i;
              divcurr_state_n   = MD_ABS_B;
              div_counter_n     = 5'd31;
              //ABS(A) = 0 - A
              alu_operand_a_o     = {32'h0  , 1'b1};
              alu_operand_b_o     = {~op_a_i, 1'b1};
          end

          MD_ABS_B: begin
              //reminder
              op_reminder_n    = { 33'h0, op_numerator_q[31]};
              //B abs value
              op_denominator_n  = div_sign_b ? alu_adder_i : op_b_i;
              divcurr_state_n   = MD_COMP;
              div_counter_n     = 5'd31;
              //ABS(B) = 0 - B
              alu_operand_a_o     = {32'h0  , 1'b1};
              alu_operand_b_o     = {~op_b_i, 1'b1};
          end

          MD_COMP: begin

            op_reminder_n     = {1'b0, next_reminder[31:0], op_numerator_q[div_counter_n]};
            op_quotient_n     = next_quotient;
            if(div_counter_q == 5'd1)
                divcurr_state_n = MD_LAST;
            else
                divcurr_state_n = MD_COMP;
            //Division
            alu_operand_a_o     = {mac_res_q[31:0], 1'b1}; //it contains the reminder
            alu_operand_b_o     = {~op_denominator_q[31:0], 1'b1}; //denominator negated + 1 to do -denominator
          end

          MD_LAST: begin

            unique case(operator_i)
              MD_OP_DIV:
                //this time we save the quotient in op_reminder_n (i.e. mac_res_q) since we do not need anymore the reminder
                op_reminder_n  = {1'b0, next_quotient};
              default:
              //this time we do not save the quotient anymore since we need only the reminder
                op_reminder_n  = {2'b0, next_reminder[31:0]};
            endcase
            //Division
            alu_operand_a_o     = {mac_res_q[31:0], 1'b1}; //it contains the reminder
            alu_operand_b_o     = {~op_denominator_q[31:0], 1'b1}; //denominator negated + 1 to do -denominator

            divcurr_state_n = MD_CHANGE_SIGN;
          end

          MD_CHANGE_SIGN: begin
              divcurr_state_n  = MD_FINISH;
              unique case(operator_i)
                MD_OP_DIV:
                  op_reminder_n = (div_change_sign) ? alu_adder_i : mac_res_q;
                default:
                  op_reminder_n = (rem_change_sign) ? alu_adder_i : mac_res_q;
              endcase
              //ABS(Quotient) = 0 - Quotient (or Reminder)
              alu_operand_a_o     = {32'h0  , 1'b1};
              alu_operand_b_o     = {~mac_res_q[31:0], 1'b1};
         end

        MD_FINISH: begin
            divcurr_state_n = MD_IDLE;
        end

        default:;
      endcase // divcurr_state_q
  end

  assign ready_o  = mult_is_ready | (divcurr_state_q == MD_FINISH);
  always_comb
  begin : mult_fsm
      mult_op_a    = op_a_i[`OP_L];
      mult_op_b    = op_b_i[`OP_L];
      sign_a       = 1'b0;
      sign_b       = 1'b0;
      accum        = mac_res_q;
      mac_res_n    = mac_res;
      mult_state_n = mult_state_q;
      mult_is_ready = 1'b0;

      unique case (mult_state_q)

        ALBL: begin
          //al*bl
          mult_op_a = op_a_i[`OP_L];
          mult_op_b = op_b_i[`OP_L];
          sign_a    = 1'b0;
          sign_b    = 1'b0;
          accum     = '0;
          mac_res_n = mac_res;
          mult_state_n = ALBH;
        end

        ALBH: begin
          //al*bh<<16
          mult_op_a = op_a_i[`OP_L];
          mult_op_b = op_b_i[`OP_H];
          sign_a    = 1'b0;
          sign_b    = signed_mode_i[1] & op_b_i[31];
          //result of AL*BL (in mac_res_q) always unsigned with no carry, so carries_q always 00
          accum     = {18'b0,mac_res_q[31:16]};
          unique case(operator_i)
            MD_OP_MULL: begin
              mac_res_n = {2'b0,mac_res[`OP_L],mac_res_q[`OP_L]};
            end
            default: begin
            //MD_OP_MULH
              mac_res_n = mac_res;
            end
          endcase

          mult_state_n = AHBL;
        end

        AHBL: begin
          //ah*bl<<16
          mult_op_a = op_a_i[`OP_H];
          mult_op_b = op_b_i[`OP_L];
          sign_a    = signed_mode_i[0] & op_a_i[31];
          sign_b    = 1'b0;
          unique case(operator_i)
            MD_OP_MULL: begin
              accum        = {18'b0,mac_res_q[31:16]};
              mac_res_n    = {2'b0,mac_res[15:0],mac_res_q[15:0]};
              mult_is_ready = 1'b1;
              mult_state_n = ALBL;
            end
            default: begin
              accum        = mac_res_q;
              mac_res_n    = mac_res;
              mult_state_n = AHBH;
            end
          endcase
        end

        AHBH: begin
        //only MD_OP_MULH here
          //ah*bh
          mult_op_a = op_a_i[`OP_H];
          mult_op_b = op_b_i[`OP_H];
          sign_a    = signed_mode_i[0] & op_a_i[31];
          sign_b    = signed_mode_i[1] & op_b_i[31];
          accum[17:0 ]  = mac_res_q[33:16];
          accum[33:18]  = {18{signed_mult & mac_res_q[33]}};
          //result of AH*BL is not signed only if signed_mode_i == 2'b00
          mac_res_n    = mac_res;
          mult_state_n = ALBL;
          mult_is_ready = 1'b1;

        end

        default:;
      endcase // mult_state_q
  end


endmodule // zeroriscy_mult
