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
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Markus Wegmann - markus.wegmann@technokrat.ch              //
//                                                                            //
// Design Name:    Execute stage                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution stage: Hosts ALU and MAC unit                    //
//                 ALU: computes additions/subtractions/comparisons           //
//                 MAC:                                                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "riscv_config.sv"

import riscv_defines::*;

module riscv_ex_stage
#(
    parameter REG_ADDR_WIDTH      = 5
)
(
  input  logic        clk,
  input  logic        rst_n,

  // ALU signals from ID stage
  input  logic [ALU_OP_WIDTH-1:0] alu_operator_i,
  input  logic [31:0] alu_operand_a_i,
  input  logic [31:0] alu_operand_b_i,
  input  logic [31:0] alu_operand_c_i,


  output logic [31:0] alu_adder_result_ex_o,

  // input from ID stage
  input  logic        branch_in_ex_i,
  input  logic [(REG_ADDR_WIDTH-1):0]  regfile_alu_waddr_i,
  input  logic        regfile_alu_we_i,
  input  logic        jal_in_ex_i,

  // directly passed through to WB stage, not used in EX
  input  logic        regfile_we_i,

  input logic         alu_req_ex_i,

  // CSR access
  input  logic        csr_access_i,
  input  logic [31:0] csr_rdata_i,

  // Output of EX stage pipeline
  output logic [(REG_ADDR_WIDTH-1):0]  regfile_waddr_wb_o,
  output logic        regfile_we_wb_o,

  // Forwarding ports : to ID stage
  output logic  [(REG_ADDR_WIDTH-1):0] regfile_alu_waddr_fw_o,
  output logic        regfile_alu_we_fw_o,
  output logic [31:0] regfile_alu_wdata_fw_o,    // forward to RF and ID/EX pipe, ALU & MUL

  // To IF: Jump and branch target and decision
  output logic [31:0] jump_target_o,
  output logic        branch_decision_o,

  // Stall Control
  input  logic        lsu_ready_ex_i, // EX part of LSU is done

  output logic        alu_ready_o,


  output logic        ex_ready_o, // EX stage ready for new data
  output logic        ex_valid_o, // EX stage gets new data
  input  logic        wb_ready_i  // WB stage ready for new data
);

  logic regfile_we_conflict; // Tests for a conflict when WB and EX want to write to a register at the same cycle.
  assign regfile_we_conflict = regfile_we_wb_o && regfile_alu_we_fw_o;

  logic [31:0] alu_result;
  logic [31:0] alu_csr_result;
  logic        alu_cmp_result;

  logic        alu_ready;

  // EX stage result mux (ALU, MAC unit, CSR)
  assign alu_csr_result         = csr_access_i ? csr_rdata_i : alu_result;

  assign regfile_alu_wdata_fw_o = jal_in_ex_i ? alu_operand_c_i : alu_csr_result; // Select return address


  assign regfile_alu_we_fw_o    = regfile_alu_we_i;
  assign regfile_alu_waddr_fw_o = regfile_alu_waddr_i;


  // branch handling
  assign branch_decision_o = alu_cmp_result;
  assign jump_target_o     = alu_adder_result_ex_o;
 


  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////



  riscv_alu_simplified alu_i
  (
    .clk                 ( clk             ),
    .rst_n               ( rst_n           ),

    .operator_i          ( alu_operator_i  ),
    .operand_a_i         ( alu_operand_a_i ),
    .operand_b_i         ( alu_operand_b_i ),

    .adder_result_o      (alu_adder_result_ex_o ),

    .result_o            ( alu_result      ),
    .comparison_result_o ( alu_cmp_result  )
  );

  assign alu_ready = 1'b1; // As there is no divider, ALU always takes only one cycle






  ///////////////////////////////////////
  // EX/WB Pipeline Register           //
  ///////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : EX_WB_Pipeline_Register
    if (~rst_n)
    begin
      regfile_waddr_wb_o   <= '0;
      regfile_we_wb_o      <= 1'b0;
    end
    else
    begin
      if (ex_valid_o) // wb_ready_i is implied
      begin
        regfile_we_wb_o    <= regfile_we_i;
        if (regfile_we_i) begin
          regfile_waddr_wb_o <= regfile_alu_waddr_i;
        end
      end else if (wb_ready_i) begin
        // we are ready for a new instruction, but there is none available,
        // so we just flush the current one out of the pipe
        regfile_we_wb_o    <= 1'b0;
      end
    end
  end

  // As valid always goes to the right and ready to the left, and we are able
  // to finish branches without going to the WB stage, ex_valid does not
  // depend on ex_ready.


  assign ex_ready_o = (alu_ready & lsu_ready_ex_i & wb_ready_i & ~regfile_we_conflict) | branch_in_ex_i;
  assign ex_valid_o = (alu_ready & lsu_ready_ex_i & wb_ready_i);


endmodule
