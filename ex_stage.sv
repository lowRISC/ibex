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
  input  logic                    mult_operator_i,
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

  localparam MULT_TYPE = 4;
  localparam ADD_TYPE  = 0; //0 shared

  logic [31:0] alu_result, mult_result, pp_acc, mult_alu_operand_a, mult_alu_operand_b;
  logic [31:0] alu_operand_a_sel, alu_operand_b_sel;
  logic        alu_cmp_result;
  logic        mult_ready, do_sub;
  logic        carry_out_mul, carry_out_mul_sel;
  logic [ALU_OP_WIDTH-1:0] alu_operator_sel;

  assign alu_operator_sel = alu_operator_i;

if(ADD_TYPE == 0)
  if(MULT_TYPE >= 8)
    assign regfile_wdata_ex_o = mult_en_i ? alu_adder_result_ex_o : alu_result;
  else
    assign regfile_wdata_ex_o = mult_en_i ? mult_result : alu_result;
else
  assign regfile_wdata_ex_o = mult_en_i ? mult_result : alu_result;

  // branch handling
  assign branch_decision_o  = alu_cmp_result;
  assign jump_target_o      = alu_adder_result_ex_o;

if(MULT_TYPE < 8) begin
  if(MULT_TYPE != 4) begin
    assign carry_out_mul_sel = carry_out_mul;
    assign alu_operand_a_sel = mult_en_i ? mult_alu_operand_a : alu_operand_a_i;
    assign alu_operand_b_sel = mult_en_i ? mult_alu_operand_b : alu_operand_b_i;
  end else begin
    assign carry_out_mul_sel = 1'b0;
    assign alu_operand_a_sel = alu_operand_a_i;
    assign alu_operand_b_sel = alu_operand_b_i;
  end
end else begin
  assign carry_out_mul_sel = 1'b0;
  assign alu_operand_a_sel = mult_en_i ? mult_result : alu_operand_a_i;
  assign alu_operand_b_sel = mult_en_i ? pp_acc : alu_operand_b_i;
end
  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////

if(ADD_TYPE == 0) begin : alu_i
  zeroriscy_alu alu_i
  (
    .operator_i          ( alu_operator_sel     ),
    .operand_a_i         ( alu_operand_a_sel    ),
    .operand_b_i         ( alu_operand_b_sel    ),
    .carry_in_i          ( carry_out_mul_sel    ),
    .adder_result_o      (alu_adder_result_ex_o ),
    .result_o            ( alu_result           ),
    .comparison_result_o ( alu_cmp_result       )
  );
end else begin : alu_i
  zeroriscy_alu alu_i
  (
    .operator_i          ( alu_operator_sel     ),
    .operand_a_i         ( alu_operand_a_i      ),
    .operand_b_i         ( alu_operand_b_i      ),
    .carry_in_i          ( carry_out_mul_sel    ),
    .adder_result_o      (alu_adder_result_ex_o ),
    .result_o            ( alu_result           ),
    .comparison_result_o ( alu_cmp_result       )
  );
end

  if (MULT_TYPE == 8) begin : mult_i
    zeroriscy_mult
    #(
      .ADD_TYPE(ADD_TYPE)
     )
    mult_i
    (
     .clk           ( clk              ),
     .rst_n         ( rst_n            ),
     .mult_en_i     ( mult_en_i        ),
     .op_a_i        ( mult_operand_a_i ),
     .op_b_i        ( mult_operand_b_i ),
     .op_acc_i      ( alu_adder_result_ex_o ),
     .ready_o       ( mult_ready       ),
     .pp_acc_o      ( pp_acc           ),
     .mult_result_o ( mult_result      )
    );
  end
  else if (MULT_TYPE == 32) begin : mult_32_i
    zeroriscy_mult32
    #(
      .ADD_TYPE(ADD_TYPE)
     )
     mult_i
     (
     .clk           ( clk              ),
     .rst_n         ( rst_n            ),
     .mult_en_i     ( mult_en_i        ),
     .op_a_i        ( mult_operand_a_i ),
     .op_b_i        ( mult_operand_b_i ),
     .op_acc_i      ( alu_adder_result_ex_o ),
     .ready_o       ( mult_ready       ),
     .pp_acc_o      ( pp_acc           ),
     .mult_result_o ( mult_result      )
    );
  end
  else if (MULT_TYPE == 33) begin : mult_33_i
    zeroriscy_mult33
    #(
      .ADD_TYPE(ADD_TYPE)
     )
     mult_i
     (
     .clk           ( clk              ),
     .rst_n         ( rst_n            ),
     .mult_en_i     ( mult_en_i        ),
     .op_a_i        ( mult_operand_a_i ),
     .op_b_i        ( mult_operand_b_i ),
     .op_acc_i      ( alu_adder_result_ex_o ),
     .ready_o       ( mult_ready       ),
     .pp_acc_o      ( pp_acc           ),
     .mult_result_o ( mult_result      )
    );
  end
  else if (MULT_TYPE == 16) begin : mult_16_i
    zeroriscy_mult16
    #(
      .ADD_TYPE(ADD_TYPE)
     )
     mult_i
     (
     .clk           ( clk              ),
     .rst_n         ( rst_n            ),
     .mult_en_i     ( mult_en_i        ),
     .op_a_i        ( mult_operand_a_i ),
     .op_b_i        ( mult_operand_b_i ),
     .op_acc_i      ( alu_adder_result_ex_o ),
     .ready_o       ( mult_ready       ),
     .pp_acc_o      ( pp_acc           ),
     .mult_result_o ( mult_result      )
    );
  end
  else if (MULT_TYPE == 0) begin : mult_h_i
    zeroriscy_mult_h
    #(
      .ADD_TYPE(ADD_TYPE)
     )
     mult_i
     (
     .clk             ( clk                   ),
     .rst_n           ( rst_n                 ),
     .mult_en_i       ( mult_en_i             ),
     .operator_i      ( mult_operator_i       ),
     .signed_mode_i   ( mult_signed_mode_i    ),
     .op_a_i          ( mult_operand_a_i      ),
     .op_b_i          ( mult_operand_b_i      ),
     .alu_adder_i     ( alu_adder_result_ex_o ),
     .ready_o         ( mult_ready            ),
     .carry_out_mul_o ( carry_out_mul         ),
     .alu_operand_a_o ( mult_alu_operand_a    ),
     .alu_operand_b_o ( mult_alu_operand_b    ),
     .mult_result_o   ( mult_result           )
    );
  end
  else if (MULT_TYPE == 1) begin : mult_hq_i
    zeroriscy_mult_hq
    #(
      .ADD_TYPE(ADD_TYPE)
     )
     mult_i
     (
     .clk             ( clk                   ),
     .rst_n           ( rst_n                 ),
     .mult_en_i       ( mult_en_i             ),
     .operator_i      ( mult_operator_i       ),
     .signed_mode_i   ( mult_signed_mode_i    ),
     .op_a_i          ( mult_operand_a_i      ),
     .op_b_i          ( mult_operand_b_i      ),
     .alu_adder_i     ( alu_adder_result_ex_o ),
     .ready_o         ( mult_ready            ),
     .carry_out_mul_o ( carry_out_mul         ),
     .alu_operand_a_o ( mult_alu_operand_a    ),
     .alu_operand_b_o ( mult_alu_operand_b    ),
     .mult_result_o   ( mult_result           )
    );
  end
  else if (MULT_TYPE == 2) begin : mult_33_hq_i
    zeroriscy_mult33_hq mult_i
     (
     .clk             ( clk                   ),
     .rst_n           ( rst_n                 ),
     .mult_en_i       ( mult_en_i             ),
     .operator_i      ( mult_operator_i       ),
     .signed_mode_i   ( mult_signed_mode_i    ),
     .op_a_i          ( mult_operand_a_i      ),
     .op_b_i          ( mult_operand_b_i      ),
     .alu_adder_i     ( alu_adder_result_ex_o ),
     .do_sub_o        ( do_sub                ),
     .ready_o         ( mult_ready            ),
     .carry_out_mul_o ( carry_out_mul         ),
     .alu_operand_a_o ( mult_alu_operand_a    ),
     .alu_operand_b_o ( mult_alu_operand_b    ),
     .mult_result_o   ( mult_result           )
    );
  end
  else if (MULT_TYPE == 4) begin : mult_16_hq_i
    zeroriscy_mult16_hq mult_i
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