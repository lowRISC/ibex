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
// Description:    Execution block: Hosts ALU and MUL/DIV unit                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "zeroriscy_config.sv"

import zeroriscy_defines::*;

module zeroriscy_ex_block
#(
  parameter RV32M      = 1
)
(

  input  logic        clk,
  input  logic        rst_n,

  // ALU signals from ID stage
  input  logic [ALU_OP_WIDTH-1:0] alu_operator_i,
  input  logic [1:0]              multdiv_operator_i,
  input  logic                    mult_en_i,
  input  logic                    div_en_i,

  input  logic [31:0]             alu_operand_a_i,
  input  logic [31:0]             alu_operand_b_i,

  input  logic  [1:0]             multdiv_signed_mode_i,
  input  logic [31:0]             multdiv_operand_a_i,
  input  logic [31:0]             multdiv_operand_b_i,

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

  localparam MULT_TYPE = 1; //0 is SLOW

  logic [31:0] alu_result, multdiv_result;

  logic [32:0] multdiv_alu_operand_b, multdiv_alu_operand_a;
  logic [33:0] alu_adder_result_ext;
  logic        alu_cmp_result, alu_is_equal_result;
  logic        multdiv_ready, multdiv_en_sel;
  logic        multdiv_en;

/*
  The multdiv_i output is never selected if RV32M=0
  At synthesis time, all the combinational and sequential logic
  from the multdiv_i module are eliminated
*/
generate
if (RV32M) begin
  assign multdiv_en_sel     = MULT_TYPE == 0 ? mult_en_i | div_en_i : div_en_i;
  assign multdiv_en         = mult_en_i | div_en_i;
end else begin
  assign multdiv_en_sel     = 1'b0;
  assign multdiv_en         = 1'b0;
end
endgenerate

  assign regfile_wdata_ex_o = multdiv_en ? multdiv_result : alu_result;

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
    .operator_i          ( alu_operator_i            ),
    .operand_a_i         ( alu_operand_a_i           ),
    .operand_b_i         ( alu_operand_b_i           ),
    .multdiv_operand_a_i ( multdiv_alu_operand_a     ),
    .multdiv_operand_b_i ( multdiv_alu_operand_b     ),
    .multdiv_en_i        ( multdiv_en_sel            ),
    .adder_result_o      ( alu_adder_result_ex_o     ),
    .adder_result_ext_o  ( alu_adder_result_ext      ),
    .result_o            ( alu_result                ),
    .comparison_result_o ( alu_cmp_result            ),
    .is_equal_result_o   ( alu_is_equal_result       )
  );

  ////////////////////////////////////////////////////////////////
  //  __  __ _   _ _   _____ ___ ____  _     ___ _____ ____     //
  // |  \/  | | | | | |_   _|_ _|  _ \| |   |_ _| ____|  _ \    //
  // | |\/| | | | | |   | |  | || |_) | |    | ||  _| | |_) |   //
  // | |  | | |_| | |___| |  | ||  __/| |___ | || |___|  _ <    //
  // |_|  |_|\___/|_____|_| |___|_|   |_____|___|_____|_| \_\   //
  //                                                            //
  ////////////////////////////////////////////////////////////////

  generate
  if (MULT_TYPE == 0) begin : multdiv_slow
    zeroriscy_multdiv_slow multdiv_i
    (
     .clk                ( clk                   ),
     .rst_n              ( rst_n                 ),
     .mult_en_i          ( mult_en_i             ),
     .div_en_i           ( div_en_i              ),
     .operator_i         ( multdiv_operator_i    ),
     .signed_mode_i      ( multdiv_signed_mode_i ),
     .op_a_i             ( multdiv_operand_a_i   ),
     .op_b_i             ( multdiv_operand_b_i   ),
     .alu_adder_ext_i    ( alu_adder_result_ext  ),
     .alu_adder_i        ( alu_adder_result_ex_o ),
     .equal_to_zero      ( alu_is_equal_result   ),
     .ready_o            ( multdiv_ready         ),
     .alu_operand_a_o    ( multdiv_alu_operand_a ),
     .alu_operand_b_o    ( multdiv_alu_operand_b ),
     .multdiv_result_o   ( multdiv_result        )
    );
  end else begin: multdiv_fast
    zeroriscy_multdiv_fast multdiv_i
     (
     .clk                ( clk                   ),
     .rst_n              ( rst_n                 ),
     .mult_en_i          ( mult_en_i             ),
     .div_en_i           ( div_en_i              ),
     .operator_i         ( multdiv_operator_i    ),
     .signed_mode_i      ( multdiv_signed_mode_i ),
     .op_a_i             ( multdiv_operand_a_i   ),
     .op_b_i             ( multdiv_operand_b_i   ),
     .alu_operand_a_o    ( multdiv_alu_operand_a ),
     .alu_operand_b_o    ( multdiv_alu_operand_b ),
     .alu_adder_ext_i    ( alu_adder_result_ext  ),
     .alu_adder_i        ( alu_adder_result_ex_o ),
     .equal_to_zero      ( alu_is_equal_result   ),
     .ready_o            ( multdiv_ready         ),
     .multdiv_result_o   ( multdiv_result        )
    );
  end
  endgenerate

  always_comb
  begin
      unique case (1'b1)
        multdiv_en:
          ex_ready_o = multdiv_ready;
        lsu_en_i:
          ex_ready_o = lsu_ready_ex_i;
        default:
          //1 Cycle case
          ex_ready_o = 1'b1;
      endcase
  end

endmodule
