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
    // CONFIG_REGION: RV32E
    `ifdef RV32E
    parameter REG_ADDR_WIDTH      = 4
    `else
    parameter REG_ADDR_WIDTH      = 5
    `endif // RV32E
)
(
  input  logic        clk,
  input  logic        rst_n,

  // ALU signals from ID stage
  input  logic [ALU_OP_WIDTH-1:0] alu_operator_i,
  input  logic [31:0] alu_operand_a_i,
  input  logic [31:0] alu_operand_b_i,
  input  logic [31:0] alu_operand_c_i,
  // CONFIG_REGION: BIT_SUPPORT
  `ifdef BIT_SUPPORT
  input  logic [ 4:0] bmask_a_i,
  input  logic [ 4:0] bmask_b_i,
  `endif // BIT_SUPPORT
  // CONFIG_REGION: VEC_SUPPORT
  `ifdef VEC_SUPPORT
  input  logic [ 1:0] imm_vec_ext_i,
  input  logic [ 1:0] alu_vec_mode_i,
  `endif // VEC_SUPPORT

  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
  // Multiplier signals
  input  logic [ 2:0] mult_operator_i,
  input  logic [31:0] mult_operand_a_i,
  input  logic [31:0] mult_operand_b_i,
  input  logic [31:0] mult_operand_c_i,
  input  logic        mult_en_i,
  input  logic        mult_sel_subword_i,
  input  logic [ 1:0] mult_signed_mode_i,
  input  logic [ 4:0] mult_imm_i,

  input  logic [31:0] mult_dot_op_a_i,
  input  logic [31:0] mult_dot_op_b_i,
  input  logic [31:0] mult_dot_op_c_i,
  input  logic [ 1:0] mult_dot_signed_i,

  output logic        mult_multicycle_o,
  `endif // MUL_SUPPORT

  // CONFIG_REGION: LSU_ADDER_SUPPORT
  `ifndef LSU_ADDER_SUPPORT
  output logic [31:0] alu_adder_result_ex_o,
  `endif // LSU_ADDER_SUPPORT

  // input from ID stage
  input  logic        branch_in_ex_i,
  input  logic [(REG_ADDR_WIDTH-1):0]  regfile_alu_waddr_i,
  input  logic        regfile_alu_we_i,

  // directly passed through to WB stage, not used in EX
  input  logic        regfile_we_i,
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  input  logic [(REG_ADDR_WIDTH-1):0]  regfile_waddr_i,
  `endif // THREE_PORT_REG_FILE

  // CSR access
  input  logic        csr_access_i,
  input  logic [31:0] csr_rdata_i,

  // Output of EX stage pipeline
  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  output logic [(REG_ADDR_WIDTH-1):0]  regfile_waddr_wb_o,
  `endif // THREE_PORT_REG_FILE
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

  output logic        ex_ready_o, // EX stage ready for new data
  output logic        ex_valid_o, // EX stage gets new data
  input  logic        wb_ready_i  // WB stage ready for new data
);

  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifndef THREE_PORT_REG_FILE
  logic regfile_we_conflict; // Tests for a conflict when WB and EX want to write to a register at the same cycle.
  assign regfile_we_conflict = regfile_we_wb_o && regfile_alu_we_fw_o;
  `endif // THREE_PORT_REG_FILE

  logic [31:0] alu_result;
  logic [31:0] alu_csr_result;
  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
  logic [31:0] mult_result;
  `endif // MUL_SUPPORT
  logic        alu_cmp_result;

  logic        alu_ready;
  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
  logic        mult_ready;
  `endif // MUL_SUPPORT

  // EX stage result mux (ALU, MAC unit, CSR)
  assign alu_csr_result         = csr_access_i ? csr_rdata_i : alu_result;

  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
  assign regfile_alu_wdata_fw_o = mult_en_i ? mult_result : alu_csr_result;
  `else
  assign regfile_alu_wdata_fw_o = alu_csr_result;
  `endif // MUL_SUPPORT


  assign regfile_alu_we_fw_o    = regfile_alu_we_i;
  assign regfile_alu_waddr_fw_o = regfile_alu_waddr_i;


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

  // CONFIG_REGION: SIMPLE_ALU
  `ifdef SIMPLE_ALU

  riscv_alu_simplified alu_i
  (
    .clk                 ( clk             ),
    .rst_n               ( rst_n           ),

    .operator_i          ( alu_operator_i  ),
    .operand_a_i         ( alu_operand_a_i ),
    .operand_b_i         ( alu_operand_b_i ),

    // CONFIG_REGION: LSU_ADDER_SUPPORT
    `ifndef LSU_ADDER_SUPPORT
    .adder_result_o      (alu_adder_result_ex_o ),
    `endif // LSU_ADDER_SUPPORT

    .result_o            ( alu_result      ),
    .comparison_result_o ( alu_cmp_result  )
  );

  assign alu_ready = 1'b1; // As there is no divider, ALU always takes only one cycle

  `else // SIMPLE_ALU

  riscv_alu alu_i
  (
    .clk                 ( clk                  ),
    .rst_n               ( rst_n                ),

    .operator_i          ( alu_operator_i       ),
    .operand_a_i         ( alu_operand_a_i      ),
    .operand_b_i         ( alu_operand_b_i      ),
    .operand_c_i         ( alu_operand_c_i      ),

    // CONFIG_REGION: VEC_SUPPORT
    `ifdef VEC_SUPPORT
    .vector_mode_i       ( alu_vec_mode_i       ),
    `endif // VEC_SUPPORT
    // CONFIG_REGION: BIT_SUPPORT
    `ifdef BIT_SUPPORT
    .bmask_a_i           ( bmask_a_i            ),
    .bmask_b_i           ( bmask_b_i            ),
    `endif // BIT_SUPPORT
    // CONFIG_REGION: VEC_SUPPORT
    `ifdef VEC_SUPPORT
    .imm_vec_ext_i       ( imm_vec_ext_i        ),
    `endif // VEC_SUPPORT

    // CONFIG_REGION: LSU_ADDER_SUPPORT
    `ifndef LSU_ADDER_SUPPORT
    .adder_result_o      (alu_adder_result_ex_o ),
    `endif // LSU_ADDER_SUPPORT

    .result_o            ( alu_result           ),
    .comparison_result_o ( alu_cmp_result       ),

    .ready_o             ( alu_ready            ),
    .ex_ready_i          ( ex_ready_o           )
  );

  `endif // SIMPLE_ALU


  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
  
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
    .clk             ( clk                  ),
    .rst_n           ( rst_n                ),

    .enable_i        ( mult_en_i            ),
    .operator_i      ( mult_operator_i      ),

    .short_subword_i ( mult_sel_subword_i   ),
    .short_signed_i  ( mult_signed_mode_i   ),

    .op_a_i          ( mult_operand_a_i     ),
    .op_b_i          ( mult_operand_b_i     ),
    .op_c_i          ( mult_operand_c_i     ),
    .imm_i           ( mult_imm_i           ),

    .dot_op_a_i      ( mult_dot_op_a_i      ),
    .dot_op_b_i      ( mult_dot_op_b_i      ),
    .dot_op_c_i      ( mult_dot_op_c_i      ),
    .dot_signed_i    ( mult_dot_signed_i    ),

    .result_o        ( mult_result          ),

    .multicycle_o    ( mult_multicycle_o    ),
    .ready_o         ( mult_ready           ),
    .ex_ready_i      ( ex_ready_o           )
  );
  `endif


  ///////////////////////////////////////
  // EX/WB Pipeline Register           //
  ///////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : EX_WB_Pipeline_Register
    if (~rst_n)
    begin
      // CONFIG_REGION: TWO_PORT_REG_FILE
      `ifdef TWO_PORT_REG_FILE
      regfile_waddr_wb_o   <= '0;
      `endif // TWO_PORT_REG_FILE
      regfile_we_wb_o      <= 1'b0;
    end
    else
    begin
      if (ex_valid_o) // wb_ready_i is implied
      begin
        regfile_we_wb_o    <= regfile_we_i;
        // CONFIG_REGION: TWO_PORT_REG_FILE
        `ifdef TWO_PORT_REG_FILE
        if (regfile_we_i) begin
          regfile_waddr_wb_o <= regfile_waddr_i;
        end
        `endif // TWO_PORT_REG_FILE
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

  // CONFIG_REGION: MUL_SUPPORT
  `ifdef MUL_SUPPORT
  assign ex_ready_o = (alu_ready & mult_ready & lsu_ready_ex_i & wb_ready_i) | branch_in_ex_i;
  assign ex_valid_o = (alu_ready & mult_ready & lsu_ready_ex_i & wb_ready_i);
  `else

  // CONFIG_REGION: THREE_PORT_REG_FILE
  `ifdef THREE_PORT_REG_FILE
  assign ex_ready_o = (alu_ready & lsu_ready_ex_i & wb_ready_i) | branch_in_ex_i;
  assign ex_valid_o = (alu_ready & lsu_ready_ex_i & wb_ready_i);
  `else // THREE_PORT_REG_FILE
  assign ex_ready_o = (alu_ready & lsu_ready_ex_i & wb_ready_i & ~regfile_we_conflict) | branch_in_ex_i;
  assign ex_valid_o = (alu_ready & lsu_ready_ex_i & wb_ready_i);
  `endif // THREE_PORT_REG_FILE

  `endif

endmodule
