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

`include "riscv_config.sv"

import zeroriscy_defines::*;

module zeroriscy_ex_block
(
  // ALU signals from ID stage
  input  logic [ALU_OP_WIDTH-1:0] alu_operator_i,
  input  logic [31:0]             alu_operand_a_i,
  input  logic [31:0]             alu_operand_b_i,

  output logic [31:0]             alu_adder_result_ex_o,
  output logic [31:0]             regfile_wdata_ex_o,

  // To IF: Jump and branch target and decision
  output logic [31:0]             jump_target_o,
  output logic                    branch_decision_o
);

  logic [31:0] alu_result;
  logic        alu_cmp_result;

  assign regfile_wdata_ex_o = alu_result;

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
    .operator_i          ( alu_operator_i       ),
    .operand_a_i         ( alu_operand_a_i      ),
    .operand_b_i         ( alu_operand_b_i      ),

    .adder_result_o      (alu_adder_result_ex_o ),

    .result_o            ( alu_result           ),
    .comparison_result_o ( alu_cmp_result       )
  );


endmodule