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
//                                                                            //
//                                                                            //
// Design Name:    Excecute stage                                             //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution stage: Hosts ALU and MAC unit                    //
//                 ALU: computes additions/subtractions/comparisons           //
//                 MAC:                                                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "riscv_defines.sv"


module riscv_ex_stage
(
  input  logic        clk,
  input  logic        rst_n,

  // ALU signals from ID stage
  input  logic [`ALU_OP_WIDTH-1:0] alu_operator_i,
  input  logic [31:0] alu_operand_a_i,
  input  logic [31:0] alu_operand_b_i,
  input  logic [31:0] alu_operand_c_i,

  input  logic        vector_mode_i,

  // Multiplier signals
  input  logic        mult_en_i,
  input  logic [1:0]  mult_sel_subword_i,
  input  logic [1:0]  mult_signed_mode_i,
  input  logic        mult_mac_en_i,

  // input from ID stage
  input  logic        branch_in_ex_i,
  input  logic [4:0]  regfile_alu_waddr_i,
  input  logic        regfile_alu_we_i,

  // directly passed through to WB stage, not used in EX
  input  logic        regfile_we_i,
  input  logic [4:0]  regfile_waddr_i,

  // CSR access
  input  logic        csr_access_i,
  input  logic [31:0] csr_rdata_i,

  // Output of EX stage pipeline
  output logic [4:0]  regfile_waddr_wb_o,
  output logic        regfile_we_wb_o,

  // Forwarding ports : to ID stage
  output logic  [4:0] regfile_alu_waddr_fw_o,
  output logic        regfile_alu_we_fw_o,
  output logic [31:0] regfile_alu_wdata_fw_o,    // forward to RF and ID/EX pipe, ALU & MUL

  // To IF: Jump and branch target and decision
  output logic [31:0] jump_target_o,
  output logic        branch_decision_o,

  // Stall Control
  input  logic        lsu_ready_ex_i, // EX part of LSU is done

  output logic        ex_ready_o, // EX stage ready for new data
  output logic        ex_valid_o, // EX stage gets new data
  input  logic        wb_ready_i  // WB stage ready for new data
);


  logic [31:0] alu_result;
  logic        alu_cmp_result;

  logic [31:0] mult_result;


  assign regfile_alu_we_fw_o    = regfile_alu_we_i;
  assign regfile_alu_waddr_fw_o = regfile_alu_waddr_i;


  // EX stage result mux (ALU, MAC unit, CSR)
  always_comb
  begin
    regfile_alu_wdata_fw_o = alu_result;

    if (mult_en_i == 1'b1)
      regfile_alu_wdata_fw_o = mult_result;

    if (csr_access_i == 1'b1)
      regfile_alu_wdata_fw_o = csr_rdata_i;
  end


  // branch handling
  assign branch_decision_o = alu_cmp_result;
  assign jump_target_o     = alu_operand_c_i;


  ////////////////////////////
  //     _    _    _   _    //
  //    / \  | |  | | | |   //
  //   / _ \ | |  | | | |   //
  //  / ___ \| |__| |_| |   //
  // /_/   \_\_____\___/    //
  //                        //
  ////////////////////////////

  riscv_alu alu_i
  (
   .operator_i          ( alu_operator_i  ),
   .operand_a_i         ( alu_operand_a_i ),
   .operand_b_i         ( alu_operand_b_i ),

   .result_o            ( alu_result      ),
   .comparison_result_o ( alu_cmp_result  )
  );


  ////////////////////////////////////////////////////////////////
  //  __  __ _   _ _   _____ ___ ____  _     ___ _____ ____     //
  // |  \/  | | | | | |_   _|_ _|  _ \| |   |_ _| ____|  _ \    //
  // | |\/| | | | | |   | |  | || |_) | |    | ||  _| | |_) |   //
  // | |  | | |_| | |___| |  | ||  __/| |___ | || |___|  _ <    //
  // |_|  |_|\___/|_____|_| |___|_|   |_____|___|_____|_| \_\   //
  //                                                            //
  ////////////////////////////////////////////////////////////////

  riscv_mult mult_i
  (
   .vector_mode_i   ( vector_mode_i        ),
   .sel_subword_i   ( mult_sel_subword_i   ),
   .signed_mode_i   ( mult_signed_mode_i   ),
   .mac_en_i        ( mult_mac_en_i        ),

   .op_a_i          ( alu_operand_a_i      ),
   .op_b_i          ( alu_operand_b_i      ),
   .mac_i           ( alu_operand_c_i      ),

   .result_o        ( mult_result          )
  );


  ///////////////////////////////////////
  // EX/WB Pipeline Register           //
  ///////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : EX_WB_Pipeline_Register
    if (rst_n == 1'b0)
    begin
      regfile_waddr_wb_o   <= 5'b0_0000;
      regfile_we_wb_o      <= 1'b0;
    end
    else
    begin
      if (ex_valid_o) // wb_ready_i is implied
      begin
        regfile_we_wb_o    <= regfile_we_i;
        regfile_waddr_wb_o <= regfile_waddr_i;
      end else if (wb_ready_i) begin
        // we are ready for a new instruction, but there is none available,
        // so we just flush the current one out of the pipe
        regfile_we_wb_o    <= 1'b0;
      end
    end
  end

  assign ex_ready_o = (lsu_ready_ex_i & wb_ready_i) | branch_in_ex_i;
  assign ex_valid_o = ex_ready_o;

endmodule
