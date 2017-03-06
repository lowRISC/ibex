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

`define OP_L 15:0
`define OP_H 31:16

module zeroriscy_mult16_hq
(
  input  logic        clk,
  input  logic        rst_n,
  input  logic        mult_en_i,
  input  logic        operator_i,
  input  logic  [1:0] signed_mode_i,
  input  logic [31:0] op_a_i,
  input  logic [31:0] op_b_i,

  output logic [31:0] mult_result_o,
  output logic        ready_o
);

  enum logic [2:0] { ALBL, ALBH, AHBL, AHBH, FINISH } mult_state_q, mult_state_n;

  logic [33:0] mul_res_ext;
  logic [34:0] mac_res_ext;
  logic [33:0] mac_res_q, mac_res_n, mac_res;
  logic [15:0] mult_op_a;
  logic [15:0] mult_op_b;
  logic [33:0] accum;
  logic sign_a,sign_b, accum_sign, signed_mult;

  always_ff @(posedge clk or negedge rst_n) begin : proc_mult_state_q
    if(~rst_n) begin
      mult_state_q   <= ALBL;
      mac_res_q      <= '0;
    end else begin
      if(mult_en_i) begin
        mult_state_q <= mult_state_n;
        mac_res_q    <= mac_res_n;
      end
    end
  end

  assign signed_mult   = (signed_mode_i != 2'b00);

  assign mult_result_o = mac_res_q[31:0];

  assign mac_res_ext = $signed({sign_a, mult_op_a})*$signed({sign_b, mult_op_b}) + $signed(accum);
  assign mac_res     = mac_res_ext[33:0];

  always_comb
  begin : mult_fsm
      ready_o   = 1'b0;
      mult_op_a = op_a_i[`OP_L];
      mult_op_b = op_b_i[`OP_L];
      sign_a    = 1'b0;
      sign_b    = 1'b0;
      accum     = mac_res_q;
      mac_res_n = mac_res;

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
            MUL_L: begin
              mac_res_n = {2'b0,mac_res[`OP_L],mac_res_q[`OP_L]};
            end
            MUL_H: begin
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
            MUL_L: begin
              accum        = {18'b0,mac_res_q[31:16]};
              mac_res_n    = {2'b0,mac_res[15:0],mac_res_q[15:0]};
              mult_state_n = FINISH;
            end
            MUL_H: begin
              accum        = mac_res_q;
              mac_res_n    = mac_res;
              mult_state_n = AHBH;
            end
          endcase
        end

        AHBH: begin
        //only MUL_H here
          //ah*bh
          mult_op_a = op_a_i[`OP_H];
          mult_op_b = op_b_i[`OP_H];
          sign_a    = signed_mode_i[0] & op_a_i[31];
          sign_b    = signed_mode_i[1] & op_b_i[31];
          accum[17:0 ]  = mac_res_q[33:16];
          accum[33:18]  = {18{signed_mult & mac_res_q[33]}};
          //result of AH*BL is not signed only if signed_mode_i == 2'b00
          mac_res_n    = mac_res;
          mult_state_n = FINISH;
        end

        FINISH: begin
          mult_state_n = ALBL;
          //ready_o must not be a timing critical signal
          ready_o      = 1'b1;
        end

        default:;
      endcase // mult_state_q
  end


endmodule // zeroriscy_mult
