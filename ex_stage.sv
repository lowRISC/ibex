// Copyright 2017 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Markus Wegmann - markus.wegmann@technokrat.ch              //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Execute stage                                              //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution block: Hosts ALU and MUL unit                    //
//                 ALU: computes additions/subtractions/comparisons           //
//                 MAC:                                                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "zeroriscy_config.sv"

import zeroriscy_defines::*;

module zeroriscy_ex_block
(

  input  logic        clk,
  input  logic        rst_n,

  // ALU signals from ID stage
  input  logic [ALU_OP_WIDTH-1:0] alu_operator_i,
  input  logic [1:0]              mult_operator_i,
  input  logic                    mult_en_i,

  input  logic [31:0]             alu_operand_a_i,
  input  logic [31:0]             alu_operand_b_i,

  input  logic  [1:0]             mult_signed_mode_i,
  input  logic [31:0]             mult_operand_a_i,
  input  logic [31:0]             mult_operand_b_i,

  output logic [31:0]             alu_adder_result_ex_o,
  output logic [31:0]             regfile_wdata_ex_o,

  // To IF: Jump and branch target and decision
  output logic [31:0]             jump_target_o,
  output logic                    branch_decision_o,

  input  logic                    lsu_en_i,

  // Stall Control
  input  logic                    lsu_ready_ex_i, // LSU is done
  output logic                    ex_ready_o      // EX stage gets new data
);

  localparam MULT_TYPE = 0; //0 is SLOW

  logic [31:0] alu_result, mult_result;

  logic [32:0] mult_alu_operand_a_sel, mult_alu_operand_b_sel, mult_alu_operand_a, mult_alu_operand_b;
  logic [33:0] alu_adder_result_ext;
  logic        alu_cmp_result, alu_is_equal_result;
  logic        mult_ready, mult_en_sel;

  assign mult_en_sel            = MULT_TYPE == 0 ? mult_en_i : 1'b0;
  assign mult_alu_operand_a_sel = MULT_TYPE == 0 ? mult_alu_operand_a : alu_operand_a_i;
  assign mult_alu_operand_b_sel = MULT_TYPE == 0 ? mult_alu_operand_b : alu_operand_b_i;

  assign regfile_wdata_ex_o = mult_en_i ? mult_result : alu_result;

  // branch handling
  assign branch_decision_o  = alu_cmp_result;
  assign jump_target_o      = alu_adder_result_ex_o;

  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////

  zeroriscy_alu alu_i
  (
    .operator_i          ( alu_operator_i         ),
    .operand_a_i         ( alu_operand_a_i        ),
    .operand_b_i         ( alu_operand_b_i        ),
    .mult_operand_a_i    ( mult_alu_operand_a_sel ),
    .mult_operand_b_i    ( mult_alu_operand_b_sel ),
    .mult_en_i           ( mult_en_sel            ),
    .adder_result_o      ( alu_adder_result_ex_o  ),
    .adder_result_ext_o  ( alu_adder_result_ext   ),
    .result_o            ( alu_result             ),
    .comparison_result_o ( alu_cmp_result         ),
    .is_equal_result_o   ( alu_is_equal_result    )
  );

  if (MULT_TYPE == 0) begin : mult_slow
    zeroriscy_mult_slow mult_i
    (
     .clk             ( clk                   ),
     .rst_n           ( rst_n                 ),
     .mult_en_i       ( mult_en_i             ),
     .operator_i      ( mult_operator_i       ),
     .signed_mode_i   ( mult_signed_mode_i    ),
     .op_a_i          ( mult_operand_a_i      ),
     .op_b_i          ( mult_operand_b_i      ),
     .alu_adder_ext_i ( alu_adder_result_ext  ),
     .alu_adder_i     ( alu_adder_result_ex_o ),
     .equal_to_zero   ( alu_is_equal_result   ),
     .ready_o         ( mult_ready            ),
     .alu_operand_a_o ( mult_alu_operand_a    ),
     .alu_operand_b_o ( mult_alu_operand_b    ),
     .mult_result_o   ( mult_result           )
    );
  end else begin: mult_fast
    zeroriscy_mult_fast mult_i
     (
     .clk             ( clk                   ),
     .rst_n           ( rst_n                 ),
     .mult_en_i       ( mult_en_i             ),
     .operator_i      ( mult_operator_i       ),
     .signed_mode_i   ( mult_signed_mode_i    ),
     .op_a_i          ( mult_operand_a_i      ),
     .op_b_i          ( mult_operand_b_i      ),
     .ready_o         ( mult_ready            ),
     .mult_result_o   ( mult_result           )
    );
  end

  always_comb
  begin
      unique case (1'b1)
        mult_en_i:
          ex_ready_o = mult_ready;
        lsu_en_i:
          ex_ready_o = lsu_ready_ex_i;
        default:
          //1 Cycle case
          ex_ready_o = 1'b1;
      endcase
  end

endmodule