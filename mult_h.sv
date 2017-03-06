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

`define OP_LL   7:0
`define OP_LH  15:8
`define OP_HL 23:16
`define OP_HH 31:24

module zeroriscy_mult_h
#(
  parameter ADD_TYPE     = 0, //0 shared
  parameter ADD_CYCL     = 1 //if ADD_CYCL is 1, ADD_TYPE must be 0
)
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic        mult_en_i,
  input  logic        operator_i,
  input  logic  [1:0] signed_mode_i,
  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,
  input  logic [31:0] alu_adder_i,

  output logic [31:0] alu_operand_a_o,
  output logic [31:0] alu_operand_b_o,
  output logic [31:0] mult_result_o,
  output logic        carry_out_mul_o,
  output logic        ready_o
);

  enum logic [3:0] { STEP0, STEP1, STEP2, STEP3, STEP4, STEP5, STEP6, STEP7, STEP8, STEP9, STEP10, STEP11, STEP12, STEP13, STEP14, STEP15 } mult_state_q, mult_state_n;
  enum logic [2:0] { MULT_00_SHIFT, MULT_08_SHIFT, MULT_16_SHIFT, MULT_24_SHIFT, MULT_32_SHIFT, MULT_40_SHIFT, MULT_48_SHIFT } shift_mul;

  logic [31:0] accum_high_q, accum_low_q;
  logic [31:0] accum_high, accum_low;
  logic [31:0] res_mul_low, res_mul_high;

  logic [ 7:0] mult_op_a;
  logic [ 7:0] mult_op_b;
  logic [63:0] mult_extended;
  logic [63:0] mult_shifted;
  logic [32:0] res_adder_low_ext;
  logic [31:0] res_adder_low;
  logic [31:0] res_adder_high;

  logic sign_a,sign_b;
  logic do_mul_n, do_mul_q;
  logic carry_out_shortadder;

  assign mult_extended = $signed({sign_a,mult_op_a})*$signed({sign_b,mult_op_b});
  assign res_mul_low   = mult_shifted[31:0 ];
  assign res_mul_high  = mult_shifted[63:32];

  assign res_adder_low_ext    = res_mul_low + accum_low;
  assign res_adder_low        = res_adder_low_ext[31:0];
  assign res_adder_high       = alu_adder_i;
  assign carry_out_shortadder = res_adder_low_ext[32];

  assign mult_result_o   = operator_i == MUL_H ? res_adder_high : res_adder_low;

  assign alu_operand_a_o = res_mul_high;
  assign alu_operand_b_o = accum_high;

  assign carry_out_mul_o = carry_out_shortadder;

  always_ff @(posedge clk or negedge rst_n) begin : proc_mult_state_q
    if(~rst_n) begin
      mult_state_q  <= STEP0;
      accum_high_q  <= '0;
      accum_low_q   <= '0;
    end else begin
      if(mult_en_i) begin
        mult_state_q   <= mult_state_n;
        accum_low_q    <= res_adder_low;
        if(operator_i == MUL_H)
          accum_high_q   <= res_adder_high;
      end
    end
  end

  always_comb
  begin : mult_fsm
      ready_o = 1'b0;
      accum_low  = accum_low_q;
      accum_high = accum_high_q;
      unique case (mult_state_q)
        STEP0: begin
            unique case(operator_i)
              MUL_L: begin
                //all*bll
                mult_op_a = op_a_i[`OP_LL];
                mult_op_b = op_b_i[`OP_LL];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                accum_low = '0;
                shift_mul = MULT_00_SHIFT;
              end
              MUL_H: begin
                //ahl*bll<<16
                mult_op_a  = op_a_i[`OP_HL];
                mult_op_b  = op_b_i[`OP_LL];
                sign_a     = 1'b0;
                sign_b     = 1'b0;
                accum_low  = '0;
                accum_high = '0;
                shift_mul  = MULT_16_SHIFT;
              end
            endcase
            mult_state_n = STEP1;
        end
        STEP1: begin
            unique case(operator_i)
              MUL_L: begin
               //all*blh<<8
                mult_op_a = op_a_i[`OP_LL];
                mult_op_b = op_b_i[`OP_LH];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_08_SHIFT;
              end
              MUL_H: begin
                //ahh*bll<<24
                mult_op_a = op_a_i[`OP_HH];
                mult_op_b = op_b_i[`OP_LL];
                sign_a    = op_a_i[31];
                sign_b    = 1'b0;
                shift_mul = MULT_24_SHIFT;
              end
            endcase
            mult_state_n = STEP2;
        end
        STEP2: begin
            unique case(operator_i)
              MUL_L: begin
                //all*bhl<<16
                mult_op_a = op_a_i[`OP_LL];
                mult_op_b = op_b_i[`OP_HL];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_16_SHIFT;
              end
              MUL_H: begin
                //ahl*blh<<24
                mult_op_a = op_a_i[`OP_HL];
                mult_op_b = op_b_i[`OP_LH];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_24_SHIFT;
              end
            endcase
            mult_state_n = STEP3;
        end
        STEP3: begin
            unique case(operator_i)
              MUL_L: begin
                //all*bhh<<24
                mult_op_a = op_a_i[`OP_LL];
                mult_op_b = op_b_i[`OP_HH];
                sign_a    = 1'b0;
                sign_b    = op_b_i[31];
                shift_mul = MULT_24_SHIFT;
              end
              MUL_H: begin
                //ahh*blh<<32
                mult_op_a = op_a_i[`OP_HH];
                mult_op_b = op_b_i[`OP_LH];
                sign_a    = op_a_i[31];
                sign_b    = 1'b0;
                shift_mul = MULT_32_SHIFT;
              end
            endcase
            mult_state_n = STEP4;
        end
        STEP4: begin
            unique case(operator_i)
              MUL_L: begin
                //alh*bll<<8
                mult_op_a = op_a_i[`OP_LH];
                mult_op_b = op_b_i[`OP_LL];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_08_SHIFT;
              end
              MUL_H: begin
                //all*bhl<<16
                mult_op_a = op_a_i[`OP_LL];
                mult_op_b = op_b_i[`OP_HL];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_16_SHIFT;
              end
            endcase
            mult_state_n = STEP5;
        end
        STEP5: begin
            unique case(operator_i)
              MUL_L: begin
                //alh*blh<<16
                mult_op_a = op_a_i[`OP_LH];
                mult_op_b = op_b_i[`OP_LH];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_16_SHIFT;
              end
              MUL_H: begin
                //alh*bhl<<24
                mult_op_a = op_a_i[`OP_LH];
                mult_op_b = op_b_i[`OP_HL];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_24_SHIFT;
              end
            endcase
            mult_state_n = STEP6;
        end
        STEP6: begin
            unique case(operator_i)
              MUL_L: begin
                //alh*bhl<<24
                mult_op_a = op_a_i[`OP_LH];
                mult_op_b = op_b_i[`OP_HL];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_24_SHIFT;
              end
              MUL_H: begin
                //all*bhh<<24
                mult_op_a = op_a_i[`OP_LL];
                mult_op_b = op_b_i[`OP_HH];
                sign_a    = 1'b0;
                sign_b    = op_b_i[31];
                shift_mul = MULT_24_SHIFT;
              end
            endcase
            mult_state_n = STEP7;
        end
        STEP7: begin
            unique case(operator_i)
              MUL_L: begin
                //ahl*bll<<16
                mult_op_a = op_a_i[`OP_HL];
                mult_op_b = op_b_i[`OP_LL];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_16_SHIFT;
              end
              MUL_H: begin
                //alh*bhh<<32
                mult_op_a = op_a_i[`OP_LH];
                mult_op_b = op_b_i[`OP_HH];
                sign_a    = 1'b0;
                sign_b    = op_b_i[31];
                shift_mul = MULT_32_SHIFT;
              end
            endcase
            mult_state_n = STEP8;
        end
        STEP8: begin
            unique case(operator_i)
              MUL_L: begin
                //ahl*blh<<24
                mult_op_a = op_a_i[`OP_HL];
                mult_op_b = op_b_i[`OP_LH];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_24_SHIFT;
              end
              MUL_H: begin
                //ahl*bhl<<32
                mult_op_a = op_a_i[`OP_HL];
                mult_op_b = op_b_i[`OP_HL];
                sign_a    = 1'b0;
                sign_b    = 1'b0;
                shift_mul = MULT_32_SHIFT;
              end
            endcase
            mult_state_n = STEP9;
        end
        STEP9: begin
            unique case(operator_i)
              MUL_L: begin
                //ahh*bll<<24
                mult_op_a = op_a_i[`OP_HH];
                mult_op_b = op_b_i[`OP_LL];
                sign_a    = op_a_i[31];
                sign_b    = 1'b0;
                shift_mul = MULT_24_SHIFT;
                mult_state_n = STEP0;
                ready_o = 1'b1;
              end
              MUL_H: begin
                //ahl*bhh<<40
                mult_op_a = op_a_i[`OP_HL];
                mult_op_b = op_b_i[`OP_HH];
                sign_a    = 1'b0;
                sign_b    = op_b_i[31];
                shift_mul = MULT_40_SHIFT;
                mult_state_n = STEP10;
              end
            endcase
        end
        STEP10: begin
          //only MUL_H here
          //ahh*bhl<<40
          mult_op_a = op_a_i[`OP_HH];
          mult_op_b = op_b_i[`OP_HL];
          sign_a    = op_a_i[31];
          sign_b    = 1'b0;
          shift_mul = MULT_40_SHIFT;
          mult_state_n = STEP11;
        end
        STEP11: begin
          //only MUL_H here
          //ahh*bhh<<48
          mult_op_a = op_a_i[`OP_HH];
          mult_op_b = op_b_i[`OP_HH];
          sign_a    = op_a_i[31];
          sign_b    = op_b_i[31];
          shift_mul = MULT_48_SHIFT;
          mult_state_n = STEP12;
        end
        STEP12: begin
          //only MUL_H here
          //all*bll
          mult_op_a = op_a_i[`OP_LL];
          mult_op_b = op_b_i[`OP_LL];
          sign_a    = 1'b0;
          sign_b    = 1'b0;
          shift_mul = MULT_00_SHIFT;
          mult_state_n = STEP13;
        end
        STEP13: begin
          //only MUL_H here
          //all*blh<<8
          mult_op_a = op_a_i[`OP_LL];
          mult_op_b = op_b_i[`OP_LH];
          sign_a    = 1'b0;
          sign_b    = 1'b0;
          shift_mul = MULT_08_SHIFT;
          mult_state_n = STEP14;
        end
        STEP14: begin
          //only MUL_H here
          //alh*bll<<8
          mult_op_a = op_a_i[`OP_LH];
          mult_op_b = op_b_i[`OP_LL];
          sign_a    = 1'b0;
          sign_b    = 1'b0;
          shift_mul = MULT_08_SHIFT;
          mult_state_n = STEP15;
        end
        STEP15: begin
          //only MUL_H here
          //alh*blh<<16
          mult_op_a = op_a_i[`OP_LH];
          mult_op_b = op_b_i[`OP_LH];
          sign_a    = 1'b0;
          sign_b    = 1'b0;
          shift_mul = MULT_16_SHIFT;
          mult_state_n = STEP0;
          ready_o = 1'b1;
        end
        default: begin
            //all*bll
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[ 7:0 ];
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_00_SHIFT;
            mult_state_n = STEP1;
        end
      endcase // mult_state_q
  end



  always_comb
  begin
    unique case (shift_mul)
        MULT_00_SHIFT:
            mult_shifted = mult_extended;
        MULT_08_SHIFT:
            mult_shifted = mult_extended <<  8;
        MULT_16_SHIFT:
            mult_shifted = mult_extended << 16;
        MULT_24_SHIFT:
            mult_shifted = mult_extended << 24;
        MULT_32_SHIFT:
            mult_shifted = mult_extended << 32;
        MULT_40_SHIFT:
            mult_shifted = mult_extended << 40;
        MULT_48_SHIFT:
            mult_shifted = mult_extended << 48;
        default:
            mult_shifted = mult_extended;
    endcase
  end

endmodule // zeroriscy_mult
