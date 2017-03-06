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


module zeroriscy_mult
#(
  parameter ADD_TYPE     = 0, //0 shared
  parameter ADD_CYCL     = 0 //if ADD_CYCL is 1, ADD_TYPE must be 0
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


  enum logic [3:0] { IDLE, STEP0, STEP1, STEP2, STEP3, STEP4, STEP5, STEP6, STEP7, STEP8, STEP9 } mult_state_q, mult_state_n;
  enum logic [1:0] { MULT_00_SHIFT, MULT_08_SHIFT, MULT_16_SHIFT, MULT_24_SHIFT } shift_mul;

  logic [31:0] accum_q;
  logic [31:0] mult_res_q;

  logic [ 7:0] mult_op_a;
  logic [ 7:0] mult_op_b;
  logic [31:0] mac_op, op_acc_int;
  logic [31:0] mult_extended;
  logic [31:0] mult_shifted;
  logic sign_a,sign_b;
  logic do_mul_n, do_mul_q;


  assign mult_extended = $signed({sign_a,mult_op_a})*$signed({sign_b,mult_op_b});
  if(ADD_CYCL)
    assign mult_result_o = mult_res_q;
  else
    assign mult_result_o = ADD_TYPE ? mult_shifted + mac_op : mult_shifted;

  assign pp_acc_o      = ADD_CYCL ? accum_q : mac_op;

  always_ff @(posedge clk or negedge rst_n) begin : proc_mult_state_q
    if(~rst_n) begin
      mult_state_q <= IDLE;
      accum_q      <= '0;
      mult_res_q   <= '0;
      do_mul_q     <= 1'b1;
    end else begin
      if(mult_en_i) begin
        mult_state_q <= mult_state_n;
        if(ADD_CYCL) begin
          if(~do_mul_q || mult_state_q == IDLE)
              accum_q <= op_acc_int;
        end else
          accum_q      <= ADD_TYPE ? mult_result_o : op_acc_i;
        if(do_mul_q && mult_state_q != IDLE)
          mult_res_q   <= ADD_CYCL ? mult_shifted : '0;
        do_mul_q     <= do_mul_n;
      end
    end
  end

if(ADD_CYCL) begin

 always_comb
  begin : mult_fsm
      ready_o    = 1'b0;
      do_mul_n   = ~do_mul_q;
      op_acc_int = op_acc_i;
      unique case (mult_state_q)
        IDLE: begin
            //idle
            do_mul_n     = 1'b1;
            op_acc_int   = '0;
            mult_state_n = STEP0;

            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = 32'h0;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_00_SHIFT;
        end
        STEP0: begin
            //all*bll
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = 32'h0;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_00_SHIFT;
            mult_state_n = ~do_mul_q ? STEP1 : STEP0;
        end
        STEP1: begin
            //all*blh<<8
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[15:8 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_08_SHIFT;
            mult_state_n = ~do_mul_q ? STEP2 : STEP1;
        end
        STEP2: begin
            //all*bhl<<16
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[23:16];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_16_SHIFT;
            mult_state_n = ~do_mul_q ? STEP3 : STEP2;
        end
        STEP3: begin
            //all*bhh<<24
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[31:24];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = op_b_i[31];
            shift_mul = MULT_24_SHIFT;
            mult_state_n = ~do_mul_q ? STEP4 : STEP3;
        end
        STEP4: begin
            //alh*bll<<8
            mult_op_a = op_a_i[15:8 ];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_08_SHIFT;
            mult_state_n = ~do_mul_q ? STEP5 : STEP4;
        end
        STEP5: begin
            //alh*blh<<16
            mult_op_a = op_a_i[15:8 ];
            mult_op_b = op_b_i[15:8 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_16_SHIFT;
            mult_state_n = ~do_mul_q ? STEP6 : STEP5;
        end
        STEP6: begin
            //alh*bhl<<24
            mult_op_a = op_a_i[15:8 ];
            mult_op_b = op_b_i[23:16];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_24_SHIFT;
            mult_state_n = ~do_mul_q ? STEP7 : STEP6;
        end
        STEP7: begin
            //ahl*bll<<16
            mult_op_a = op_a_i[23:16];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_16_SHIFT;
            mult_state_n = ~do_mul_q ? STEP8 : STEP7;
        end
        STEP8: begin
            //ahl*blh<<24
            mult_op_a = op_a_i[23:16];
            mult_op_b = op_b_i[15:8 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_24_SHIFT;
            mult_state_n = ~do_mul_q ? STEP9 : STEP8;
        end
        STEP9: begin
            //ahh*bll<<24
            mult_op_a = op_a_i[31:24];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = accum_q;
            sign_a    = op_a_i[31];
            sign_b    = 1'b0;
            shift_mul = MULT_24_SHIFT;
            mult_state_n = ~do_mul_q ? IDLE : STEP9;
            ready_o   = ~do_mul_q;
        end
        default: begin
            //idle
            do_mul_n     = 1'b1;
            op_acc_int   = '0;
            mult_state_n = STEP0;

            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = 32'h0;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_00_SHIFT;
        end
      endcase // mult_state_q
  end
end else begin
  always_comb
  begin : mult_fsm
      ready_o = 1'b0;
      unique case (mult_state_q)
        STEP0: begin
            //all*bll
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = 32'h0;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_00_SHIFT;
            mult_state_n = STEP1;
        end
        STEP1: begin
            //all*blh<<8
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[15:8 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_08_SHIFT;
            mult_state_n = STEP2;
        end
        STEP2: begin
            //all*bhl<<16
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[23:16];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_16_SHIFT;
            mult_state_n = STEP3;
        end
        STEP3: begin
            //all*bhh<<24
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[31:24];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = op_b_i[31];
            shift_mul = MULT_24_SHIFT;
            mult_state_n = STEP4;
        end
        STEP4: begin
            //alh*bll<<8
            mult_op_a = op_a_i[15:8 ];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_08_SHIFT;
            mult_state_n = STEP5;
        end
        STEP5: begin
            //alh*blh<<16
            mult_op_a = op_a_i[15:8 ];
            mult_op_b = op_b_i[15:8 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_16_SHIFT;
            mult_state_n = STEP6;
        end
        STEP6: begin
            //alh*bhl<<24
            mult_op_a = op_a_i[15:8 ];
            mult_op_b = op_b_i[23:16];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_24_SHIFT;
            mult_state_n = STEP7;
        end
        STEP7: begin
            //ahl*bll<<16
            mult_op_a = op_a_i[23:16];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_16_SHIFT;
            mult_state_n = STEP8;
        end
        STEP8: begin
            //ahl*blh<<24
            mult_op_a = op_a_i[23:16];
            mult_op_b = op_b_i[15:8 ];
            mac_op    = accum_q;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_24_SHIFT;
            mult_state_n = STEP9;
        end
        STEP9: begin
            //ahh*bll<<24
            mult_op_a = op_a_i[31:24];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = accum_q;
            sign_a    = op_a_i[31];
            sign_b    = 1'b0;
            shift_mul = MULT_24_SHIFT;
            mult_state_n = STEP0;
            ready_o = 1'b1;
        end
        default: begin
            //all*bll
            mult_op_a = op_a_i[ 7:0 ];
            mult_op_b = op_b_i[ 7:0 ];
            mac_op    = 32'h0;
            sign_a    = 1'b0;
            sign_b    = 1'b0;
            shift_mul = MULT_00_SHIFT;
            mult_state_n = STEP1;
        end
      endcase // mult_state_q
  end
end


  always_comb
  begin
    unique case (shift_mul)
        MULT_00_SHIFT:
            mult_shifted = mult_extended;
        MULT_08_SHIFT:
            mult_shifted = {mult_extended[23:0],8'h0};
        MULT_16_SHIFT:
            mult_shifted = {mult_extended[15:0],16'h0};
        MULT_24_SHIFT:
            mult_shifted = {mult_extended[ 7:0],24'h0};
        default:
            mult_shifted = mult_extended;
    endcase
  end

//  assign result_o      = mult_shifted + mac_op;

endmodule // zeroriscy_mult
