// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

/**
 * Instruction Decode Stage
 *
 * Decode stage of the core. It decodes the instructions and hosts the register
 * file.
 */

`include "prim_assert.sv"
`include "dv_fcov_macros.svh"

module ibex_id_stage import ibex_pkg::*; #(
  parameter bit               RV32E           = 0,
  parameter rv32m_e           RV32M           = RV32MFast,
  parameter rv32b_e           RV32B           = RV32BNone,
  parameter bit               DataIndTiming   = 1'b0,
  parameter bit               BranchTargetALU = 0,
  parameter bit               WritebackStage  = 0,
  parameter bit               BranchPredictor = 0,
  parameter bit               ResetAll        = 1'b0,
  parameter bit               MemECC          = 1'b0,
  parameter bit               XInterface      = 1'b1,
  parameter bit               MemInterface    = 1'b0
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  output logic                      ctrl_busy_o,
  output logic                      illegal_insn_o,

  // Interface to IF stage
  input  logic                      instr_valid_i,
  input  logic [31:0]               instr_rdata_i,         // from IF-ID pipeline registers
  input  logic [31:0]               instr_rdata_alu_i,     // from IF-ID pipeline registers
  input  logic [15:0]               instr_rdata_c_i,       // from IF-ID pipeline registers
  input  logic                      instr_is_compressed_i,
  input  logic                      instr_bp_taken_i,
  output logic                      instr_req_o,
  output logic                      instr_first_cycle_id_o,
  output logic                      instr_valid_clear_o,   // kill instr in IF-ID reg
  output logic                      id_in_ready_o,         // ID stage is ready for next instr
  output logic                      icache_inval_o,

  // Jumps and branches
  input  logic                      branch_decision_i,

  // IF and ID stage signals
  output logic                      pc_set_o,
  output pc_sel_e                   pc_mux_o,
  output logic                      nt_branch_mispredict_o,
  output logic [31:0]               nt_branch_addr_o,
  output exc_pc_sel_e               exc_pc_mux_o,
  output exc_cause_t                exc_cause_o,

  input  logic                      illegal_c_insn_i,
  input  logic                      instr_fetch_err_i,
  input  logic                      instr_fetch_err_plus2_i,

  input  logic [31:0]               pc_id_i,

  // Stalls
  input  logic                      ex_valid_i,       // EX stage has valid output
  input  logic                      lsu_resp_valid_i, // LSU has valid output, or is done
  // ALU
  output alu_op_e                   alu_operator_ex_o,
  output logic [31:0]               alu_operand_a_ex_o,
  output logic [31:0]               alu_operand_b_ex_o,

  // Multicycle Operation Stage Register
  input  logic [1:0]                imd_val_we_ex_i,
  input  logic [33:0]               imd_val_d_ex_i[2],
  output logic [33:0]               imd_val_q_ex_o[2],

  // Branch target ALU
  output logic [31:0]               bt_a_operand_o,
  output logic [31:0]               bt_b_operand_o,

  // MUL, DIV
  output logic                      mult_en_ex_o,
  output logic                      div_en_ex_o,
  output logic                      mult_sel_ex_o,
  output logic                      div_sel_ex_o,
  output md_op_e                    multdiv_operator_ex_o,
  output logic  [1:0]               multdiv_signed_mode_ex_o,
  output logic [31:0]               multdiv_operand_a_ex_o,
  output logic [31:0]               multdiv_operand_b_ex_o,
  output logic                      multdiv_ready_id_o,

  // CSR
  output logic                      csr_access_o,
  output csr_op_e                   csr_op_o,
  output logic                      csr_op_en_o,
  output logic                      csr_save_if_o,
  output logic                      csr_save_id_o,
  output logic                      csr_save_wb_o,
  output logic                      csr_restore_mret_id_o,
  output logic                      csr_restore_dret_id_o,
  output logic                      csr_save_cause_o,
  output logic [31:0]               csr_mtval_o,
  input  priv_lvl_e                 priv_mode_i,
  input  logic                      csr_mstatus_tw_i,
  input  logic                      illegal_csr_insn_i,
  input  logic                      data_ind_timing_i,

  // Interface to load store unit
  output logic                      lsu_req_o,
  output logic                      lsu_we_o,
  output logic [1:0]                lsu_type_o,
  output logic                      lsu_sign_ext_o,
  output logic [31:0]               lsu_wdata_o,

  input  logic                      lsu_req_done_i, // Data req to LSU is complete and
                                                    // instruction can move to writeback
                                                    // (only relevant where writeback stage is
                                                    // present)

  input  logic                      lsu_addr_incr_req_i,
  input  logic [31:0]               lsu_addr_last_i,
  input  logic [31:0]               lsu_rdata_i,
  output logic [3:0]                lsu_x_mem_be_o,

  // Interrupt signals
  input  logic                      csr_mstatus_mie_i,
  input  logic                      irq_pending_i,
  input  irqs_t                     irqs_i,
  input  logic                      irq_nm_i,
  output logic                      nmi_mode_o,

  input  logic                      lsu_load_err_i,
  input  logic                      lsu_store_err_i,
  input  logic                      lsu_load_intg_err_i,

  // Debug Signal
  output logic                      debug_mode_o,
  output dbg_cause_e                debug_cause_o,
  output logic                      debug_csr_save_o,
  input  logic                      debug_req_i,
  input  logic                      debug_single_step_i,
  input  logic                      debug_ebreakm_i,
  input  logic                      debug_ebreaku_i,
  input  logic                      trigger_match_i,

  // Write back signal
  input  logic [31:0]               result_ex_i,
  input  logic [31:0]               csr_rdata_i,

  // Register file read
  output logic [4:0]                rf_raddr_a_o,
  input  logic [31:0]               rf_rdata_a_i,
  output logic [4:0]                rf_raddr_b_o,
  input  logic [31:0]               rf_rdata_b_i,
  output logic                      rf_ren_a_o,
  output logic                      rf_ren_b_o,

  // Register file write (via writeback)
  output logic [4:0]                rf_waddr_id_o,
  output logic [31:0]               rf_wdata_id_o,
  output logic                      rf_we_id_o,
  output logic                      rf_rd_a_wb_match_o,
  output logic                      rf_rd_b_wb_match_o,

  // Register write information from writeback (for resolving data hazards)
  input  logic [4:0]                rf_waddr_wb_i,
  input  logic [31:0]               rf_wdata_fwd_wb_i,
  input  logic                      rf_write_wb_i,

  output logic                      en_wb_o,
  output wb_instr_type_e            instr_type_wb_o,
  output logic                      instr_perf_count_id_o,
  input  logic                      ready_wb_i,
  input  logic                      outstanding_load_wb_i,
  input  logic                      outstanding_store_wb_i,

  // Performance Counters
  output logic                      perf_jump_o,    // executing a jump instr
  output logic                      perf_branch_o,  // executing a branch instr
  output logic                      perf_tbranch_o, // executing a taken branch instr
  output logic                      perf_dside_wait_o, // instruction in ID/EX is awaiting memory
                                                        // access to finish before proceeding
  output logic                      perf_mul_wait_o,
  output logic                      perf_div_wait_o,

  // RVFI Signals
  output logic                      instr_id_internal_done_o,
  output logic                      instr_id_xif_offl_o,
  output logic                      instr_id_xif_done_o,
  output logic [4:0]                instr_rs1_o,
  output logic [4:0]                instr_rs2_o,
  output logic [4:0]                instr_rs3_o,
  output logic [4:0]                instr_rd_o,

  // X-Interface Signals
  // ECS Signals
  input  logic [5:0]                ecs_rd_i,
  output logic [5:0]                ecs_wr_o,
  output logic [2:0]                ecs_wen_o,

  // Privilege mode output
  output ibex_pkg::priv_lvl_e       priv_mode_lsu_xif_o,
  output logic                      priv_mode_lsu_xif_en_o,

  // Issue Interface
  output logic                      x_issue_valid_o,
  input  logic                      x_issue_ready_i,
  output x_issue_req_t              x_issue_req_o,
  input  x_issue_resp_t             x_issue_resp_i,

  // Commit Interface
  output logic                      x_commit_valid_o,
  output x_commit_t                 x_commit_o,

  // Memory Interface
  input  logic                      x_mem_valid_i,
  output logic                      x_mem_ready_o,
  input  x_mem_req_t                x_mem_req_i,
  output x_mem_resp_t               x_mem_resp_o,

  // Memory Result Interface
  output logic                      x_mem_result_valid_o,
  output x_mem_result_t             x_mem_result_o,

  // Result Interface
  input  logic                      x_result_valid_i,
  output logic                      x_result_ready_o,
  input  x_result_t                 x_result_i,

  // To ex block
  output logic                      x_mem_lsu_req_o,

  // For assertion only
  output logic                      outstanding_xif_load_store_o
);

  // Decoder/Controller, ID stage internal signals
  logic        illegal_insn_dec;
  logic        illegal_insn_id;
  logic        illegal_dret_insn;
  logic        illegal_umode_insn;
  logic        ebrk_insn;
  logic        mret_insn_dec;
  logic        dret_insn_dec;
  logic        ecall_insn_dec;
  logic        wfi_insn_dec;

  logic        wb_exception;
  logic        id_exception;

  logic        branch_in_dec;
  logic        branch_set, branch_set_raw, branch_set_raw_d;
  logic        branch_jump_set_done_q, branch_jump_set_done_d;
  logic        branch_not_set;
  logic        branch_taken;
  logic        jump_in_dec;
  logic        jump_set_dec;
  logic        jump_set, jump_set_raw;

  logic        instr_first_cycle;
  logic        instr_executing_spec;
  logic        instr_executing;
  logic        instr_internal_done;
  logic        controller_run;
  logic        stall_ld_a_hz;
  logic        stall_ld_b_hz;
  logic        stall_ld_hz;
  logic        stall_mem;
  logic        stall_multdiv;
  logic        stall_branch;
  logic        stall_jump;
  logic        stall_offl;
  logic        stall_external;
  logic        stall_external_exc;
  logic        stall_external_rd_hz;
  logic        stall_xif_wb;
  logic        stall_id;
  logic        stall_wb;
  logic        flush_id;
  logic        multicycle_done;

  // X-Interface signals
  logic        x_issue_handshake;
  logic        x_issue_candidate;
  logic        x_issue_accept;
  logic        x_issue_get_rs3;
  logic        x_issue_use_rs3;
  logic        imd_val_we_x_issue;
  logic        x_result_handshake;
  logic        x_result_wb_en;
  logic        x_result_exc;
  logic [5:0]  x_result_exccode;
  logic        x_result_err;
  logic        rf_rd_a_match_xif;
  logic        rf_rd_b_match_xif;
  logic        x_mem_load_err;
  logic        x_mem_store_err;
  logic        x_mem_lsu_req;

  assign x_mem_lsu_req_o = x_mem_lsu_req;

  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_j_type;
  logic [31:0] zimm_rs1_type;

  logic [31:0] imm_a;       // contains the immediate for operand b
  logic [31:0] imm_b;       // contains the immediate for operand b

  // Register file interface

  rf_wd_sel_e  rf_wdata_sel;
  logic        rf_we_dec, rf_we_raw;
  logic        rf_ren_a, rf_ren_b;
  logic        rf_ren_a_dec, rf_ren_b_dec;

  // Read enables should only be asserted for valid and legal instructions
  assign rf_ren_a = (instr_valid_i & ~instr_fetch_err_i & ~x_issue_candidate & rf_ren_a_dec) |
                    (instr_valid_i & x_issue_candidate);
  assign rf_ren_b = (instr_valid_i & ~instr_fetch_err_i & ~x_issue_candidate & rf_ren_b_dec) |
                    (instr_valid_i & x_issue_candidate);

  assign rf_ren_a_o = rf_ren_a;
  assign rf_ren_b_o = rf_ren_b;

  logic [4:0]  rf_waddr_dec;
  logic [31:0] rf_wdata_mux;

  logic [31:0] rf_rdata_a_fwd;
  logic [31:0] rf_rdata_b_fwd;

  // ALU Control
  alu_op_e     alu_operator;
  op_a_sel_e   alu_op_a_mux_sel, alu_op_a_mux_sel_dec;
  op_b_sel_e   alu_op_b_mux_sel, alu_op_b_mux_sel_dec;
  logic        alu_multicycle_dec;
  logic        stall_alu;

  logic [33:0] imd_val_d[2], imd_val_q[2];

  op_a_sel_e   bt_a_mux_sel;
  imm_b_sel_e  bt_b_mux_sel;

  imm_a_sel_e  imm_a_mux_sel;
  imm_b_sel_e  imm_b_mux_sel, imm_b_mux_sel_dec;

  // Multiplier Control
  logic        mult_en_id, mult_en_dec; // use integer multiplier
  logic        div_en_id, div_en_dec;   // use integer division or reminder
  logic        multdiv_en_dec;
  md_op_e      multdiv_operator;
  logic [1:0]  multdiv_signed_mode;

  // Data Memory Control
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic        lsu_req, lsu_req_dec;
  logic        data_req_allowed;
  logic        outstanding_memory_access;

  // CSR control
  logic        csr_pipe_flush;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;

  /////////////
  // LSU Mux //
  /////////////

  // Misaligned loads/stores result in two aligned loads/stores, compute second address
  assign alu_op_a_mux_sel = lsu_addr_incr_req_i ? OP_A_FWD        : alu_op_a_mux_sel_dec;
  assign alu_op_b_mux_sel = lsu_addr_incr_req_i ? OP_B_IMM        : alu_op_b_mux_sel_dec;
  assign imm_b_mux_sel    = lsu_addr_incr_req_i ? IMM_B_INCR_ADDR : imm_b_mux_sel_dec;

  ///////////////////
  // Operand MUXES //
  ///////////////////

  // Main ALU immediate MUX for Operand A
  assign imm_a = (imm_a_mux_sel == IMM_A_Z) ? zimm_rs1_type : '0;

  // Main ALU MUX for Operand A
  always_comb begin : alu_operand_a_mux
    unique case (alu_op_a_mux_sel)
      OP_A_REG_A:  alu_operand_a = rf_rdata_a_fwd;
      OP_A_FWD:    alu_operand_a = lsu_addr_last_i;
      OP_A_CURRPC: alu_operand_a = pc_id_i;
      OP_A_IMM:    alu_operand_a = imm_a;
      default:     alu_operand_a = pc_id_i;
    endcase
  end

  if (BranchTargetALU) begin : g_btalu_muxes
    // Branch target ALU operand A mux
    always_comb begin : bt_operand_a_mux
      unique case (bt_a_mux_sel)
        OP_A_REG_A:  bt_a_operand_o = rf_rdata_a_fwd;
        OP_A_CURRPC: bt_a_operand_o = pc_id_i;
        default:     bt_a_operand_o = pc_id_i;
      endcase
    end

    // Branch target ALU operand B mux
    always_comb begin : bt_immediate_b_mux
      unique case (bt_b_mux_sel)
        IMM_B_I:         bt_b_operand_o = imm_i_type;
        IMM_B_B:         bt_b_operand_o = imm_b_type;
        IMM_B_J:         bt_b_operand_o = imm_j_type;
        IMM_B_INCR_PC:   bt_b_operand_o = instr_is_compressed_i ? 32'h2 : 32'h4;
        default:         bt_b_operand_o = instr_is_compressed_i ? 32'h2 : 32'h4;
      endcase
    end

    // Reduced main ALU immediate MUX for Operand B
    always_comb begin : immediate_b_mux
      unique case (imm_b_mux_sel)
        IMM_B_I:         imm_b = imm_i_type;
        IMM_B_S:         imm_b = imm_s_type;
        IMM_B_U:         imm_b = imm_u_type;
        IMM_B_INCR_PC:   imm_b = instr_is_compressed_i ? 32'h2 : 32'h4;
        IMM_B_INCR_ADDR: imm_b = 32'h4;
        default:         imm_b = 32'h4;
      endcase
    end
    `ASSERT(IbexImmBMuxSelValid, instr_valid_i |-> imm_b_mux_sel inside {
        IMM_B_I,
        IMM_B_S,
        IMM_B_U,
        IMM_B_INCR_PC,
        IMM_B_INCR_ADDR})
  end else begin : g_nobtalu
    op_a_sel_e  unused_a_mux_sel;
    imm_b_sel_e unused_b_mux_sel;

    assign unused_a_mux_sel = bt_a_mux_sel;
    assign unused_b_mux_sel = bt_b_mux_sel;
    assign bt_a_operand_o   = '0;
    assign bt_b_operand_o   = '0;

    // Full main ALU immediate MUX for Operand B
    always_comb begin : immediate_b_mux
      unique case (imm_b_mux_sel)
        IMM_B_I:         imm_b = imm_i_type;
        IMM_B_S:         imm_b = imm_s_type;
        IMM_B_B:         imm_b = imm_b_type;
        IMM_B_U:         imm_b = imm_u_type;
        IMM_B_J:         imm_b = imm_j_type;
        IMM_B_INCR_PC:   imm_b = instr_is_compressed_i ? 32'h2 : 32'h4;
        IMM_B_INCR_ADDR: imm_b = 32'h4;
        default:         imm_b = 32'h4;
      endcase
    end
    `ASSERT(IbexImmBMuxSelValid, instr_valid_i |-> imm_b_mux_sel inside {
        IMM_B_I,
        IMM_B_S,
        IMM_B_B,
        IMM_B_U,
        IMM_B_J,
        IMM_B_INCR_PC,
        IMM_B_INCR_ADDR})
  end

  // ALU MUX for Operand B
  assign alu_operand_b = (alu_op_b_mux_sel == OP_B_IMM) ? imm_b : rf_rdata_b_fwd;

  /////////////////////////////////////////
  // Multicycle Operation Stage Register //
  /////////////////////////////////////////

  // The multicycle operation register is shared for
  // - Integer Multiplications (Ex Block)
  // - Integer Divisions (Ex Block)
  // - Multicycle ALU Operations (Ex Block)
  // - Latching register contents for offloading ternary operations

  always_comb begin
    imd_val_d = imd_val_q;
    unique case(1'b1)
      |imd_val_we_ex_i: begin
        for (int i = 0; i < 2; i++) begin
          imd_val_d[i] = imd_val_we_ex_i[i] ? imd_val_d_ex_i[i] : imd_val_q[i];
        end
      end
      imd_val_we_x_issue: begin
        imd_val_d[0] = {2'b00, rf_rdata_a_fwd};
      end
      default:;
    endcase
  end

  for (genvar i = 0; i < 2; i++) begin : gen_intermediate_val_reg
    always_ff @(posedge clk_i or negedge rst_ni) begin : intermediate_val_reg
      if (!rst_ni) begin
        imd_val_q[i] <= '0;
      end else begin
        imd_val_q[i] <= imd_val_d[i];
      end
    end
  end

  assign imd_val_q_ex_o = imd_val_q;

  ///////////////////////
  // Register File MUX //
  ///////////////////////

  // Suppress register write if there is an illegal CSR access or instruction is not executing
  assign rf_we_id_o = (rf_we_raw & instr_executing & ~illegal_csr_insn_i) | x_result_wb_en;

  // Register file write data mux
  always_comb begin : rf_wdata_id_mux
    unique case (rf_wdata_sel)
      RF_WD_EX:  rf_wdata_mux = result_ex_i;
      RF_WD_CSR: rf_wdata_mux = csr_rdata_i;
      default:   rf_wdata_mux = result_ex_i;
    endcase
  end

  /////////////
  // Decoder //
  /////////////

  ibex_decoder #(
    .RV32E          (RV32E),
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU),
    .XInterface     (XInterface)
  ) decoder_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // controller
    .illegal_insn_o(illegal_insn_dec),
    .ebrk_insn_o   (ebrk_insn),
    .mret_insn_o   (mret_insn_dec),
    .dret_insn_o   (dret_insn_dec),
    .ecall_insn_o  (ecall_insn_dec),
    .wfi_insn_o    (wfi_insn_dec),
    .jump_set_o    (jump_set_dec),
    .branch_taken_i(branch_taken),
    .icache_inval_o(icache_inval_o),

    // from IF-ID pipeline register
    .instr_first_cycle_i(instr_first_cycle),
    .instr_rdata_i      (instr_rdata_i),
    .instr_rdata_alu_i  (instr_rdata_alu_i),
    .illegal_c_insn_i   (illegal_c_insn_i),

    // immediates
    .imm_a_mux_sel_o(imm_a_mux_sel),
    .imm_b_mux_sel_o(imm_b_mux_sel_dec),
    .bt_a_mux_sel_o (bt_a_mux_sel),
    .bt_b_mux_sel_o (bt_b_mux_sel),

    .imm_i_type_o   (imm_i_type),
    .imm_s_type_o   (imm_s_type),
    .imm_b_type_o   (imm_b_type),
    .imm_u_type_o   (imm_u_type),
    .imm_j_type_o   (imm_j_type),
    .zimm_rs1_type_o(zimm_rs1_type),

    // register file
    .rf_wdata_sel_o(rf_wdata_sel),
    .rf_we_o       (rf_we_dec),

    .rf_raddr_a_o(rf_raddr_a_o),
    .rf_raddr_b_o(rf_raddr_b_o),
    .rf_waddr_o  (rf_waddr_dec),
    .rf_ren_a_o  (rf_ren_a_dec),
    .rf_ren_b_o  (rf_ren_b_dec),

    // ALU
    .alu_operator_o    (alu_operator),
    .alu_op_a_mux_sel_o(alu_op_a_mux_sel_dec),
    .alu_op_b_mux_sel_o(alu_op_b_mux_sel_dec),
    .alu_multicycle_o  (alu_multicycle_dec),

    // MULT & DIV
    .mult_en_o            (mult_en_dec),
    .div_en_o             (div_en_dec),
    .mult_sel_o           (mult_sel_ex_o),
    .div_sel_o            (div_sel_ex_o),
    .multdiv_operator_o   (multdiv_operator),
    .multdiv_signed_mode_o(multdiv_signed_mode),

    // CSRs
    .csr_access_o(csr_access_o),
    .csr_op_o    (csr_op_o),

    // LSU
    .data_req_o           (lsu_req_dec),
    .data_we_o            (lsu_we),
    .data_type_o          (lsu_type),
    .data_sign_extension_o(lsu_sign_ext),

    // jump/branches
    .jump_in_dec_o  (jump_in_dec),
    .branch_in_dec_o(branch_in_dec),

    // X-Interface signals
    .x_issue_handshake_i(x_issue_handshake),
    .x_issue_get_rs3_i  (x_issue_get_rs3),
    .x_issue_use_rs3_o  (x_issue_use_rs3),

    // To RVFI
    .instr_rs1_o(instr_rs1_o),
    .instr_rs2_o(instr_rs2_o),
    .instr_rs3_o(instr_rs3_o),
    .instr_rd_o (instr_rd_o)
  );

  /////////////////////////////////
  // CSR-related pipline flushes //
  /////////////////////////////////
  always_comb begin : csr_pipeline_flushes
    csr_pipe_flush = 1'b0;

    // A pipeline flush is needed to let the controller react after modifying certain CSRs:
    // - When enabling interrupts, pending IRQs become visible to the controller only during
    //   the next cycle. If during that cycle the core disables interrupts again, it does not
    //   see any pending IRQs and consequently does not start to handle interrupts.
    // - When modifying debug CSRs - TODO: Check if this is really needed
    if (csr_op_en_o == 1'b1 && (csr_op_o == CSR_OP_WRITE || csr_op_o == CSR_OP_SET)) begin
      if (csr_num_e'(instr_rdata_i[31:20]) == CSR_MSTATUS   ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_MIE) begin
        csr_pipe_flush = 1'b1;
      end
    end else if (csr_op_en_o == 1'b1 && csr_op_o != CSR_OP_READ) begin
      if (csr_num_e'(instr_rdata_i[31:20]) == CSR_DCSR      ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_DPC       ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_DSCRATCH0 ||
          csr_num_e'(instr_rdata_i[31:20]) == CSR_DSCRATCH1) begin
        csr_pipe_flush = 1'b1;
      end
    end
  end

  ////////////////
  // Controller //
  ////////////////

  // "Executing DRET outside of Debug Mode causes an illegal instruction exception."
  // [Debug Spec v0.13.2, p.41]
  assign illegal_dret_insn  = dret_insn_dec & ~debug_mode_o;
  // Some instructions can only be executed in M-Mode
  assign illegal_umode_insn = (priv_mode_i != PRIV_LVL_M) &
                              // MRET must be in M-Mode. TW means trap WFI to M-Mode.
                              (mret_insn_dec | (csr_mstatus_tw_i & wfi_insn_dec));

  assign illegal_insn_o = instr_valid_i &
      (illegal_insn_id | illegal_dret_insn | illegal_umode_insn);

  ibex_controller #(
    .WritebackStage (WritebackStage),
    .BranchPredictor(BranchPredictor),
    .MemECC(MemECC),
    .XInterface(XInterface)
  ) controller_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .ctrl_busy_o(ctrl_busy_o),

    // decoder related signals
    .illegal_insn_i  (illegal_insn_o),
    .ecall_insn_i    (ecall_insn_dec),
    .mret_insn_i     (mret_insn_dec),
    .dret_insn_i     (dret_insn_dec),
    .wfi_insn_i      (wfi_insn_dec),
    .ebrk_insn_i     (ebrk_insn),
    .csr_pipe_flush_i(csr_pipe_flush),

    // from IF-ID pipeline
    .instr_valid_i          (instr_valid_i),
    .instr_i                (instr_rdata_i),
    .instr_compressed_i     (instr_rdata_c_i),
    .instr_is_compressed_i  (instr_is_compressed_i),
    .instr_bp_taken_i       (instr_bp_taken_i),
    .instr_fetch_err_i      (instr_fetch_err_i),
    .instr_fetch_err_plus2_i(instr_fetch_err_plus2_i),
    .pc_id_i                (pc_id_i),

    // to IF-ID pipeline
    .instr_valid_clear_o(instr_valid_clear_o),
    .id_in_ready_o      (id_in_ready_o),
    .controller_run_o   (controller_run),

    // to prefetcher
    .instr_req_o           (instr_req_o),
    .pc_set_o              (pc_set_o),
    .pc_mux_o              (pc_mux_o),
    .nt_branch_mispredict_o(nt_branch_mispredict_o),
    .exc_pc_mux_o          (exc_pc_mux_o),
    .exc_cause_o           (exc_cause_o),

    // LSU
    .lsu_addr_last_i(lsu_addr_last_i),
    .load_err_i     (lsu_load_err_i | x_mem_load_err),
    .load_intg_err_i(lsu_load_intg_err_i),
    .store_err_i    (lsu_store_err_i | x_mem_store_err),
    .wb_exception_o (wb_exception),
    .id_exception_o (id_exception),

    // jump/branch control
    .branch_set_i     (branch_set),
    .branch_not_set_i (branch_not_set),
    .jump_set_i       (jump_set),

    // interrupt signals
    .csr_mstatus_mie_i(csr_mstatus_mie_i),
    .irq_pending_i    (irq_pending_i),
    .irqs_i           (irqs_i),
    .irq_nm_ext_i     (irq_nm_i | x_result_err),
    .nmi_mode_o       (nmi_mode_o),

    // CSR Controller Signals
    .csr_save_if_o        (csr_save_if_o),
    .csr_save_id_o        (csr_save_id_o),
    .csr_save_wb_o        (csr_save_wb_o),
    .csr_restore_mret_id_o(csr_restore_mret_id_o),
    .csr_restore_dret_id_o(csr_restore_dret_id_o),
    .csr_save_cause_o     (csr_save_cause_o),
    .csr_mtval_o          (csr_mtval_o),
    .priv_mode_i          (priv_mode_i),

    // Debug Signal
    .debug_mode_o       (debug_mode_o),
    .debug_cause_o      (debug_cause_o),
    .debug_csr_save_o   (debug_csr_save_o),
    .debug_req_i        (debug_req_i),
    .debug_single_step_i(debug_single_step_i),
    .debug_ebreakm_i    (debug_ebreakm_i),
    .debug_ebreaku_i    (debug_ebreaku_i),
    .trigger_match_i    (trigger_match_i),

    .stall_id_i(stall_id),
    .stall_wb_i(stall_wb),
    .flush_id_o(flush_id),
    .ready_wb_i(ready_wb_i),

    // Performance Counters
    .perf_jump_o   (perf_jump_o),
    .perf_tbranch_o(perf_tbranch_o),

    .x_issue_handshake_i(x_issue_handshake),
    .x_result_exc_i     (x_result_exc),
    .x_result_exccode_i (x_result_exccode)
  );

  assign multdiv_en_dec  = mult_en_dec | div_en_dec;

  assign lsu_req_o       = x_mem_lsu_req | lsu_req;
  assign lsu_req         = instr_executing ? data_req_allowed & lsu_req_dec  : 1'b0;
  assign mult_en_id      = instr_executing ? mult_en_dec                     : 1'b0;
  assign div_en_id       = instr_executing ? div_en_dec                      : 1'b0;

  // csr_op_en_o is set when CSR access should actually happen.
  // csv_access_o is set when CSR access instruction is present and is used to compute whether a CSR
  // access is illegal. A combinational loop would be created if csr_op_en_o was used along (as
  // asserting it for an illegal csr access would result in a flush that would need to deassert it).
  assign csr_op_en_o             = csr_access_o & instr_executing & instr_id_internal_done_o;

  assign alu_operator_ex_o           = alu_operator;

  assign mult_en_ex_o                = mult_en_id;
  assign div_en_ex_o                 = div_en_id;

  assign multdiv_operator_ex_o       = multdiv_operator;
  assign multdiv_signed_mode_ex_o    = multdiv_signed_mode;
  assign multdiv_operand_a_ex_o      = rf_rdata_a_fwd;
  assign multdiv_operand_b_ex_o      = rf_rdata_b_fwd;

  ////////////////////////
  // Branch set control //
  ////////////////////////

  if (BranchTargetALU && !DataIndTiming) begin : g_branch_set_direct
    // Branch set fed straight to controller with branch target ALU
    // (condition pass/fail used same cycle as generated instruction request)
    assign branch_set_raw      = branch_set_raw_d;
  end else begin : g_branch_set_flop
    // SEC_CM: CORE.DATA_REG_SW.SCA
    // Branch set flopped without branch target ALU, or in fixed time execution mode
    // (condition pass/fail used next cycle where branch target is calculated)
    logic branch_set_raw_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        branch_set_raw_q <= 1'b0;
      end else begin
        branch_set_raw_q <= branch_set_raw_d;
      end
    end

    // Branches always take two cycles in fixed time execution mode, with or without the branch
    // target ALU (to avoid a path from the branch decision into the branch target ALU operand
    // muxing).
    assign branch_set_raw      = (BranchTargetALU && !data_ind_timing_i) ? branch_set_raw_d :
                                                                           branch_set_raw_q;

  end

  // Track whether the current instruction in ID/EX has done a branch or jump set.
  assign branch_jump_set_done_d = (branch_set_raw | jump_set_raw | branch_jump_set_done_q) &
    ~instr_valid_clear_o;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      branch_jump_set_done_q <= 1'b0;
    end else begin
      branch_jump_set_done_q <= branch_jump_set_done_d;
    end
  end

  // the _raw signals from the state machine may be asserted for multiple cycles when
  // instr_executing_spec is asserted and instr_executing is not asserted. This may occur where
  // a memory error is seen or a there are outstanding memory accesses (indicate a load or store is
  // in the WB stage). The branch or jump speculatively begins the fetch but is held back from
  // completing until it is certain the outstanding access hasn't seen a memory error. This logic
  // ensures only the first cycle of a branch or jump set is sent to the controller to prevent
  // needless extra IF flushes and fetches.
  assign jump_set        = jump_set_raw        & ~branch_jump_set_done_q;
  assign branch_set      = branch_set_raw      & ~branch_jump_set_done_q;

  // Branch condition is calculated in the first cycle and flopped for use in the second cycle
  // (only used in fixed time execution mode to determine branch destination).
  if (DataIndTiming) begin : g_sec_branch_taken
    // SEC_CM: CORE.DATA_REG_SW.SCA
    logic branch_taken_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        branch_taken_q <= 1'b0;
      end else begin
        branch_taken_q <= branch_decision_i;
      end
    end

    assign branch_taken = ~data_ind_timing_i | branch_taken_q;

  end else begin : g_nosec_branch_taken

    // Signal unused without fixed time execution mode - only taken branches will trigger
    // branch_set_raw
    assign branch_taken = 1'b1;

  end

  // Holding branch_set/jump_set high for more than one cycle should not cause a functional issue.
  // However it could generate needless prefetch buffer flushes and instruction fetches. The ID/EX
  // designs ensures that this never happens for non-predicted branches.
  `ASSERT(NeverDoubleBranch, branch_set & ~instr_bp_taken_i |=> ~branch_set)
  `ASSERT(NeverDoubleJump, jump_set & ~instr_bp_taken_i |=> ~jump_set)

  //////////////////////////////
  // Branch not-taken address //
  //////////////////////////////

  if (BranchPredictor) begin : g_calc_nt_addr
    assign nt_branch_addr_o = pc_id_i + (instr_is_compressed_i ? 32'd2 : 32'd4);
  end else begin : g_n_calc_nt_addr
    assign nt_branch_addr_o = 32'd0;
  end

  ///////////////
  // ID-EX FSM //
  ///////////////

  typedef enum logic { FIRST_CYCLE, MULTI_CYCLE } id_fsm_e;
  id_fsm_e id_fsm_q, id_fsm_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : id_pipeline_reg
    if (!rst_ni) begin
      id_fsm_q <= FIRST_CYCLE;
    end else if (instr_executing) begin
      id_fsm_q <= id_fsm_d;
    end
  end

  // ID/EX stage can be in two states, FIRST_CYCLE and MULTI_CYCLE. An instruction enters
  // MULTI_CYCLE if it requires multiple cycles to complete regardless of stalls and other
  // considerations. An instruction may be held in FIRST_CYCLE if it's unable to begin executing
  // (this is controlled by instr_executing).

  always_comb begin
    id_fsm_d                = id_fsm_q;
    rf_we_raw               = rf_we_dec;
    stall_multdiv           = 1'b0;
    stall_jump              = 1'b0;
    stall_branch            = 1'b0;
    stall_alu               = 1'b0;
    branch_set_raw_d        = 1'b0;
    branch_not_set          = 1'b0;
    jump_set_raw            = 1'b0;
    perf_branch_o           = 1'b0;

    if (instr_executing_spec) begin
      unique case (id_fsm_q)
        FIRST_CYCLE: begin
          unique case (1'b1)
            lsu_req_dec: begin
              if (!WritebackStage) begin
                // LSU operation
                id_fsm_d    = MULTI_CYCLE;
              end else begin
                if(~lsu_req_done_i) begin
                  id_fsm_d  = MULTI_CYCLE;
                end
              end
            end
            multdiv_en_dec: begin
              // MUL or DIV operation
              if (~ex_valid_i) begin
                // When single-cycle multiply is configured mul can finish in the first cycle so
                // only enter MULTI_CYCLE state if a result isn't immediately available
                id_fsm_d      = MULTI_CYCLE;
                rf_we_raw     = 1'b0;
                stall_multdiv = 1'b1;
              end
            end
            branch_in_dec: begin
              // cond branch operation
              // All branches take two cycles in fixed time execution mode, regardless of branch
              // condition.
              // SEC_CM: CORE.DATA_REG_SW.SCA
              id_fsm_d         = (data_ind_timing_i || (!BranchTargetALU && branch_decision_i)) ?
                                     MULTI_CYCLE : FIRST_CYCLE;
              stall_branch     = (~BranchTargetALU & branch_decision_i) | data_ind_timing_i;
              branch_set_raw_d = (branch_decision_i | data_ind_timing_i);

              if (BranchPredictor) begin
                branch_not_set = ~branch_decision_i;
              end

              perf_branch_o = 1'b1;
            end
            jump_in_dec: begin
              // uncond branch operation
              // BTALU means jumps only need one cycle
              id_fsm_d      = BranchTargetALU ? FIRST_CYCLE : MULTI_CYCLE;
              stall_jump    = ~BranchTargetALU;
              jump_set_raw  = jump_set_dec;
            end
            alu_multicycle_dec: begin
              stall_alu     = 1'b1;
              id_fsm_d      = MULTI_CYCLE;
              rf_we_raw     = 1'b0;
            end
            default: begin
              id_fsm_d      = FIRST_CYCLE;
            end
          endcase
        end

        MULTI_CYCLE: begin
          if(multdiv_en_dec) begin
            rf_we_raw       = rf_we_dec & ex_valid_i;
          end

          if (multicycle_done & ready_wb_i) begin
            id_fsm_d        = FIRST_CYCLE;
          end else begin
            stall_multdiv   = multdiv_en_dec;
            stall_branch    = branch_in_dec;
            stall_jump      = jump_in_dec;
          end
        end

        default: begin
          id_fsm_d          = FIRST_CYCLE;
        end
      endcase
    end
  end

  // Note for the two-stage configuration ready_wb_i is always set
  assign multdiv_ready_id_o = ready_wb_i;

  `ASSERT(StallIDIfMulticycle, (id_fsm_q == FIRST_CYCLE) & (id_fsm_d == MULTI_CYCLE) |-> stall_id)


  // Stall ID/EX stage for reason that relates to instruction in ID/EX, update assertion below if
  // modifying this.
  assign stall_id = stall_ld_hz | stall_mem | stall_multdiv | stall_jump | stall_branch |
                    stall_alu | stall_offl | stall_external | stall_xif_wb;

  // Generally illegal instructions have no reason to stall, however they must still stall waiting
  // for outstanding memory requests so exceptions related to them take priority over the illegal
  // instruction exception.
  `ASSERT(IllegalInsnStallMustBeMemStall, illegal_insn_o & stall_id |-> stall_mem &
    ~(stall_ld_hz | stall_multdiv | stall_jump | stall_branch |
      stall_alu | stall_offl | stall_external | stall_xif_wb))

  assign instr_internal_done = ~stall_id & ~flush_id & instr_executing & ~x_issue_candidate;

  // Signal instruction in ID is in it's first cycle. It can remain in its
  // first cycle if it is stalled.
  assign instr_first_cycle      = instr_valid_i & (id_fsm_q == FIRST_CYCLE);
  // Used by RVFI to know when to capture register read data
  // Used by ALU to access RS3 if ternary instruction.
  assign instr_first_cycle_id_o = instr_first_cycle;

  if (WritebackStage) begin : gen_stall_mem
    // Register read address matches write address in WB
    logic rf_rd_a_wb_match;
    logic rf_rd_b_wb_match;
    // Hazard between registers being read and written
    logic rf_rd_a_hz;
    logic rf_rd_b_hz;

    logic instr_kill;

    assign multicycle_done = lsu_req_dec ? ~stall_mem : ex_valid_i;

    // Is a memory access ongoing that isn't finishing this cycle
    assign outstanding_memory_access = (outstanding_load_wb_i | outstanding_store_wb_i) &
                                       ~lsu_resp_valid_i;

    // Can start a new memory access if any previous one has finished or is finishing
    assign data_req_allowed = ~outstanding_memory_access;

    // Instruction won't execute because:
    // - There is a pending exception in writeback
    //   The instruction in ID/EX will be flushed and the core will jump to an exception handler
    // - The controller isn't running instructions
    //   This either happens in preparation for a flush and jump to an exception handler e.g. in
    //   response to an IRQ or debug request or whilst the core is sleeping or resetting/fetching
    //   first instruction in which case any valid instruction in ID/EX should be ignored.
    // - There was an error on instruction fetch
    assign instr_kill = instr_fetch_err_i |
                        wb_exception      |
                        id_exception      |
                        ~controller_run;

    // With writeback stage instructions must be prevented from executing if there is:
    // - A load hazard
    // - A pending memory access
    //   If it receives an error response this results in a precise exception from WB so ID/EX
    //   instruction must not execute until error response is known).
    // - A load/store error
    //   This will cause a precise exception for the instruction in WB so ID/EX instruction must not
    //   execute
    //
    // instr_executing_spec is a speculative signal. It indicates an instruction can execute
    // assuming there are no exceptions from writeback and any outstanding memory access won't
    // receive an error. It is required so branch and jump requests don't factor in an incoming dmem
    // error (that in turn would factor directly into imem requests leading to a feedthrough path).
    //
    // instr_executing is the full signal, it will only allow execution once any potential
    // exceptions from writeback have been resolved.
    assign instr_executing_spec = instr_valid_i         &
                                  ~instr_fetch_err_i    &
                                  controller_run        &
                                  ~stall_external_rd_hz &
                                  ~stall_ld_hz;

    assign instr_executing = instr_valid_i              &
                             ~instr_kill                &
                             ~stall_ld_hz               &
                             ~stall_external            &
                             ~stall_xif_wb              &
                             ~outstanding_memory_access;

    `ASSERT(IbexExecutingSpecIfExecuting, instr_executing |-> instr_executing_spec)

    `ASSERT(IbexStallIfValidInstrNotExecuting,
      instr_valid_i & ~instr_kill & ~instr_executing |-> stall_id)

    `ASSERT(IbexCannotRetireWithPendingExceptions,
      instr_internal_done |-> ~(wb_exception | outstanding_memory_access))

    // Stall for reasons related to memory:
    // * There is an outstanding memory access that won't resolve this cycle (need to wait to allow
    //   precise exceptions)
    // * There is a load/store request not being granted or which is unaligned and waiting to issue
    //   a second request (needs to stay in ID for the address calculation)
    assign stall_mem = instr_valid_i &
                       (outstanding_memory_access | (lsu_req_dec & ~lsu_req_done_i));

    // If we stall a load in ID for any reason, it must not make an LSU request
    // (otherwide we might issue two requests for the same instruction)
    `ASSERT(IbexStallMemNoRequest,
      instr_valid_i & lsu_req_dec & ~instr_internal_done |-> ~lsu_req_done_i)

    assign rf_rd_a_wb_match = (rf_waddr_wb_i == rf_raddr_a_o) & |rf_raddr_a_o;
    assign rf_rd_b_wb_match = (rf_waddr_wb_i == rf_raddr_b_o) & |rf_raddr_b_o;

    assign rf_rd_a_wb_match_o = rf_rd_a_wb_match;
    assign rf_rd_b_wb_match_o = rf_rd_b_wb_match;

    // If instruction is reading register that load will be writing stall in
    // ID until load is complete. No need to stall when reading zero register.
    assign rf_rd_a_hz = rf_rd_a_wb_match & rf_ren_a;
    assign rf_rd_b_hz = rf_rd_b_wb_match & rf_ren_b;

    // If instruction is read register that writeback is writing forward writeback data to read
    // data. Note this doesn't factor in load data as it arrives too late, such hazards are
    // resolved via a stall (see above).
    assign rf_rdata_a_fwd = rf_rd_a_match_xif ? x_result_i.data :
                            rf_rd_a_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_a_i;
    assign rf_rdata_b_fwd = rf_rd_b_match_xif ? x_result_i.data :
                            rf_rd_b_wb_match & rf_write_wb_i ? rf_wdata_fwd_wb_i : rf_rdata_b_i;

    assign stall_ld_a_hz = outstanding_load_wb_i & rf_rd_a_hz;
    assign stall_ld_b_hz = outstanding_load_wb_i & rf_rd_b_hz;
    assign stall_ld_hz   = stall_ld_a_hz | stall_ld_b_hz;

    assign instr_type_wb_o = (~lsu_req_dec | x_result_wb_en) ? WB_INSTR_OTHER :
                               lsu_we                        ? WB_INSTR_STORE :
                                                               WB_INSTR_LOAD;

    assign instr_id_internal_done_o = instr_internal_done & ready_wb_i;

    // Stall ID/EX as instruction in ID/EX cannot proceed to writeback yet
    assign stall_wb = instr_internal_done & ~ready_wb_i;

    assign perf_dside_wait_o = instr_valid_i & ~instr_kill &
                               (outstanding_memory_access | stall_ld_hz);
  end else begin : gen_no_stall_mem

    assign outstanding_memory_access = 1'b0;

    assign multicycle_done = lsu_req_dec ? lsu_resp_valid_i : ex_valid_i;

    assign data_req_allowed = instr_first_cycle;

    // Without Writeback Stage always stall the first cycle of a load/store.
    // Then stall until it is complete
    assign stall_mem = instr_valid_i & (lsu_req_dec & (~lsu_resp_valid_i | instr_first_cycle));

    // No load hazards without Writeback Stage
    assign stall_ld_a_hz = 1'b0;
    assign stall_ld_b_hz = 1'b0;
    assign stall_ld_hz   = stall_ld_a_hz | stall_ld_b_hz;

    // Without writeback stage any valid instruction that hasn't seen an error will execute
    assign instr_executing_spec = instr_valid_i      &
                                  ~instr_fetch_err_i &
                                  ~stall_external    &
                                  ~stall_xif_wb      &
                                  controller_run;
    assign instr_executing = instr_executing_spec;

    `ASSERT(IbexStallIfValidInstrNotExecuting,
      instr_valid_i & ~instr_fetch_err_i & ~instr_executing & controller_run |-> stall_id)

    // No data forwarding without writeback stage so always take source register data direct from
    // register file
    assign rf_rdata_a_fwd = rf_rd_a_match_xif ? x_result_i.data : rf_rdata_a_i;
    assign rf_rdata_b_fwd = rf_rd_b_match_xif ? x_result_i.data : rf_rdata_b_i;

    assign rf_rd_a_wb_match_o = 1'b0;
    assign rf_rd_b_wb_match_o = 1'b0;

    // Unused Writeback stage only IO & wiring
    // Assign inputs and internal wiring to unused signals to satisfy lint checks
    // Tie-off outputs to constant values
    logic unused_data_req_done_ex;
    logic [4:0] unused_rf_waddr_wb;
    logic unused_rf_write_wb;
    logic unused_outstanding_load_wb;
    logic unused_outstanding_store_wb;
    logic unused_wb_exception;
    logic [31:0] unused_rf_wdata_fwd_wb;
    logic unused_id_exception;

    assign unused_data_req_done_ex     = lsu_req_done_i;
    assign unused_rf_waddr_wb          = rf_waddr_wb_i;
    assign unused_rf_write_wb          = rf_write_wb_i;
    assign unused_outstanding_load_wb  = outstanding_load_wb_i;
    assign unused_outstanding_store_wb = outstanding_store_wb_i;
    assign unused_wb_exception         = wb_exception;
    assign unused_rf_wdata_fwd_wb      = rf_wdata_fwd_wb_i;
    assign unused_id_exception         = id_exception;

    assign instr_type_wb_o = WB_INSTR_OTHER;
    assign stall_wb        = 1'b0;

    assign perf_dside_wait_o = instr_executing & lsu_req_dec & ~lsu_resp_valid_i;

    assign instr_id_internal_done_o = instr_internal_done;
  end

  assign instr_id_xif_offl_o = x_issue_accept;
  assign instr_id_xif_done_o = x_result_handshake;

  // Signal which instructions to count as retired in minstret, all traps along with ebrk and
  // ecall instructions are not counted.
  assign instr_perf_count_id_o = ~ebrk_insn & ~ecall_insn_dec &
      ~illegal_insn_id & ~instr_fetch_err_i;

  // An instruction is ready to move to the writeback stage (or retire if there is no writeback
  // stage)
  assign en_wb_o = instr_internal_done | x_result_wb_en;

  assign perf_mul_wait_o = stall_multdiv & mult_en_dec;
  assign perf_div_wait_o = stall_multdiv & div_en_dec;

  /////////////////////////
  // X-Interface Support //
  /////////////////////////

  // Outstanding external instruction cause pipeline stall when:
  // 1. Instruction is valid, and
  // 2. The current instruction is an internal instruction, and
  // 3a. Source register is not clean, or
  // 3b. External instruction can cause exception.
  assign stall_external = stall_external_exc | stall_external_rd_hz;

  assign x_issue_handshake  = x_issue_valid_o & x_issue_ready_i;
  assign x_result_handshake = x_result_valid_i & x_result_ready_o;
  assign stall_xif_wb       = x_result_wb_en;

  assign rf_rd_a_match_xif = (x_result_i.rd == rf_raddr_a_o) & |rf_raddr_a_o & x_result_wb_en;
  assign rf_rd_b_match_xif = (x_result_i.rd == rf_raddr_b_o) & |rf_raddr_b_o & x_result_wb_en;

  if (XInterface) begin : gen_x_interface

    /////////////////////
    // Issue Interface //
    /////////////////////

    logic x_issue_valid_candidate;
    logic x_issue_reject;
    // registerfile related signals
    logic                x_issue_rs_a_valid;
    logic                x_issue_rs_b_valid;
    logic [X_NUM_RS-1:0] x_issue_rs_valid;
    // register values
    logic [X_NUM_RS-1:0][X_RFR_WIDTH-1:0] x_issue_rs_value;
    // id signals from issue-commit buffer
    logic [X_ID_WIDTH-1:0] x_issue_id;
    logic                  x_issue_icb_valid;
    // respond signals
    logic x_issue_wb;
    logic x_issue_exc;
    logic x_issue_ls;
    logic unused_x_issue_ecsw;
    logic unused_x_issue_dw;
    logic unused_x_issue_dr;
    // For candidate signal
    logic mem_xif;

    // An valid instruction is an offload candidate for issue interface when:
    // 1. It can not be recognized by the decoder, or
    // 2. It access an illegal address in CSR.
    // Both csr addr and external memory instruction use the same adder,
    // csr instruction is illegal only if there will not be any external memory instruction.
    assign x_issue_candidate = illegal_insn_dec | (illegal_csr_insn_i & ~mem_xif);

    assign x_issue_valid_candidate = instr_valid_i & x_issue_candidate &
                                     ~instr_fetch_err_i & ~wb_exception & controller_run;

    // Output a valid signal when:
    // 1. There is a valid offload candidate, and
    // 3. Issue-commit buffer is ready for a new issue.
    assign x_issue_valid_o = x_issue_valid_candidate & x_issue_icb_valid;

    // When offloading instruction, pipeline will stall if:
    // 1. Waiting for the ready signal from X-Interface, or
    // 2. Waiting for issue-commit buffer to be ready or destination register to be clean
    assign stall_offl = x_issue_valid_candidate & ~(x_issue_icb_valid & x_issue_ready_i);

    // Interface output request signals
    assign x_issue_req_o.instr     = instr_rdata_i;
    assign x_issue_req_o.mode      = priv_mode_i;
    assign x_issue_req_o.id        = x_issue_id;
    assign x_issue_req_o.rs        = x_issue_rs_value;
    assign x_issue_req_o.rs_valid  = x_issue_rs_valid;
    assign x_issue_req_o.ecs       = ecs_rd_i;
    assign x_issue_req_o.ecs_valid = 1'b1;

    // Interface respond signals, to issue-commit buffer
    assign x_issue_accept      = x_issue_handshake & x_issue_resp_i.accept;
    assign x_issue_reject      = x_issue_handshake & ~x_issue_resp_i.accept;
    assign x_issue_wb          = x_issue_resp_i.writeback;
    assign x_issue_exc         = x_issue_resp_i.exc;
    assign x_issue_ls          = x_issue_resp_i.loadstore;
    assign unused_x_issue_ecsw = x_issue_resp_i.ecswrite;
    assign unused_x_issue_dw   = x_issue_resp_i.dualwrite;
    assign unused_x_issue_dr   = x_issue_resp_i.dualread;

    // RF read block.
    if (X_NUM_RS == 2) begin : gen_rs_2
      // 2 source operands
      assign x_issue_rs_value[0] = rf_rdata_a_fwd;
      assign x_issue_rs_value[1] = rf_rdata_b_fwd;

      assign x_issue_rs_valid[0] = x_issue_rs_a_valid;
      assign x_issue_rs_valid[1] = x_issue_rs_b_valid;

      assign x_issue_get_rs3     = 1'b0;
      assign imd_val_we_x_issue  = 1'b0;

      logic unused_x_issue_use_rs3;
      assign unused_x_issue_use_rs3 = x_issue_use_rs3;
    end else begin : gen_rs_3
      // 3 source operands

      // Read rs3 next cycle when:
      // 1. The instruction is a valid offload candidate, and
      // 2. The value read from rs1 is valid, and
      // 3. The instruction has not been accepted or rejected by the accelerator.
      assign x_issue_get_rs3 = instr_valid_i & x_issue_candidate &
                               x_issue_rs_a_valid & ~x_issue_handshake;

      assign imd_val_we_x_issue  = ~x_issue_use_rs3 & x_issue_get_rs3;

      always_comb begin
        x_issue_rs_value[0] = rf_rdata_a_fwd;
        x_issue_rs_value[1] = rf_rdata_b_fwd;
        x_issue_rs_value[2] = rf_rdata_a_fwd;

        x_issue_rs_valid[0] = 1'b0;
        x_issue_rs_valid[1] = 1'b0;
        x_issue_rs_valid[2] = 1'b0;

        unique case (x_issue_use_rs3)
          1'b0: begin
            x_issue_rs_valid[0] = x_issue_rs_a_valid;
            x_issue_rs_valid[1] = x_issue_rs_b_valid;
            x_issue_rs_valid[2] = 1'b0;
          end

          1'b1: begin
            // rs1 is latched in intermediate value register
            x_issue_rs_value[0] = imd_val_q[0][31:0];
            x_issue_rs_valid[0] = 1'b1;
            x_issue_rs_valid[1] = x_issue_rs_b_valid;
            x_issue_rs_valid[2] = x_issue_rs_a_valid;
          end
          default:;
        endcase
      end
    end

    //////////////////////
    // Commit Interface //
    //////////////////////

    logic [X_ID_WIDTH-1:0] x_commit_id;
    logic                  x_commit_kill;
    // The signals are generated from issue-commit buffer
    assign x_commit_o.id          = x_commit_id;
    assign x_commit_o.commit_kill = x_commit_kill;

    //////////////////////
    // Result Interface //
    //////////////////////

    logic [X_ID_WIDTH-1:0]       x_result_id;
    logic [X_RFW_WIDTH-1:0]      x_result_data;
    logic [4:0]                  x_result_rd;
    logic [X_RFW_WIDTH/XLEN-1:0] x_result_we;
    logic [5:0]                  x_result_ecsdata;
    logic [2:0]                  x_result_ecswe;
    logic                        unused_x_result_dbg;

    // Input result signals
    assign x_result_id      = x_result_i.id;
    assign x_result_data    = x_result_i.data;
    assign x_result_rd      = x_result_i.rd;
    assign x_result_we      = x_result_i.we;
    assign x_result_ecsdata = x_result_i.ecsdata;
    assign x_result_ecswe   = x_result_i.ecswe;
    assign x_result_exc     = x_result_i.exc & x_result_handshake;
    assign x_result_exccode = x_result_i.exccode;
    assign x_result_err     = x_result_i.err & x_result_handshake;

    // Handshake signal
    assign x_result_ready_o = ready_wb_i;
    // Writeback enable signal
    assign x_result_wb_en   = x_result_handshake & x_result_we;
    // Multiplexers for writeback
    assign rf_waddr_id_o    = x_result_wb_en ? x_result_rd   : rf_waddr_dec;
    assign rf_wdata_id_o    = x_result_wb_en ? x_result_data : rf_wdata_mux;
    // ECS signals
    assign ecs_wen_o        = x_result_handshake ? x_result_ecswe : 3'b0;
    assign ecs_wr_o         = x_result_ecsdata;

    assign unused_x_result_dbg = x_result_i.dbg;

    ////////////////////////////////////////
    // Memory and Memory Result Interface //
    ////////////////////////////////////////

    // Scoreboard Signals
    logic [X_ID_WIDTH-1:0] x_mem_id_d;
    logic                  x_mem_commit;
    logic                  x_mem_result_fin;
    logic [X_ID_WIDTH-1:0] x_mem_result_id;
    logic                  x_mem_result_err;

    if (MemInterface) begin : gen_mem_interface
      logic [31:0]              x_mem_addr;
      logic                     x_mem_we;
      logic [2:0]               x_mem_size;
      logic [1:0]               x_mem_type;
      logic [X_MEM_WIDTH/8-1:0] x_mem_be;
      logic [1:0]               unused_mem_attr;
      logic [X_MEM_WIDTH-1:0]   x_mem_wdata;
      logic                     x_mem_last_d, x_mem_last_q;
      logic                     x_mem_spec;
      logic [X_ID_WIDTH-1:0]    x_mem_id_q;
      logic                     x_mem_handshake;
      logic                     x_mem_size_err;

      // State mechine for memory and memory result interface
      typedef enum logic [1:0] { MEM_IDLE, MEM_LSU_REQ, MEM_WAIT_RESULT } x_mem_fsm_e;
      x_mem_fsm_e x_mem_fsm_q, x_mem_fsm_d;

      // Input request signals
      assign x_mem_id_d   = x_mem_req_i.id;
      assign x_mem_addr   = x_mem_req_i.addr;
      assign x_mem_we     = x_mem_req_i.we;
      assign x_mem_size   = x_mem_req_i.size;
      assign x_mem_be     = x_mem_req_i.be;
      assign x_mem_wdata  = x_mem_req_i.wdata;
      assign x_mem_last_d = x_mem_req_i.last;
      assign x_mem_spec   = x_mem_req_i.spec;

      assign unused_mem_attr = x_mem_req_i.attr;

      // LSU privillege level
      assign priv_mode_lsu_xif_o    = x_mem_req_i.mode;
      assign priv_mode_lsu_xif_en_o = 1'b1;

      // Output respond signals
      // Load and store exceptions supportted now are bus errors,
      // the signals of which are transmitted through memory result interface.
      assign x_mem_resp_o.exc     = x_mem_load_err | x_mem_store_err;
      assign x_mem_resp_o.exccode = x_mem_load_err ? 6'd05 : (x_mem_store_err ? 6'd07 : '0);
      assign x_mem_resp_o.dbg     = 1'b0;

      // Output memory result signals
      assign x_mem_result_id      = x_mem_id_q;
      assign x_mem_result_o.id    = x_mem_id_q;
      // Mux to avoid x in output, which will cause assertion failure in lockstep
      assign x_mem_result_o.rdata = x_mem_result_valid_o ? lsu_rdata_i : '0;
      assign x_mem_result_o.err   = x_mem_result_err;
      assign x_mem_result_o.dbg   = 1'b0;

      // Handshake
      assign x_mem_handshake = x_mem_valid_i & x_mem_ready_o;

      // Deal with memory request type
      always_comb begin
        x_mem_type     = 2'b00;
        x_mem_size_err = 1'b0;
        unique case (x_mem_size)
          // Byte
          3'b000: begin
            x_mem_type     = 2'b10;
          end
          // Half word
          3'b001: begin
            x_mem_type     = 2'b01;
          end
          // Word
          3'b010: begin
            x_mem_type     = 2'b00;
          end
          // Other values are illegal, raise an exception
          3'b011,
          3'b100,
          3'b101,
          3'b110,
          3'b111: begin
            x_mem_size_err = 1'b1;
          end
          default: begin
          end
        endcase
      end

      // LSU signals
      assign lsu_we_o       = x_mem_lsu_req ? x_mem_we    : lsu_we;
      assign lsu_type_o     = x_mem_lsu_req ? x_mem_type  : lsu_type;
      assign lsu_sign_ext_o = x_mem_lsu_req ? 1'b0        : lsu_sign_ext;
      assign lsu_wdata_o    = x_mem_lsu_req ? x_mem_wdata : rf_rdata_b_fwd;

      // LSU address signals
      assign alu_operand_a_ex_o = x_mem_lsu_req ? x_mem_addr : alu_operand_a;
      assign alu_operand_b_ex_o = x_mem_lsu_req ? (lsu_addr_incr_req_i ? 32'h4 : 32'h0) :
                                                  alu_operand_b;

      always_comb begin
        x_mem_fsm_d          = x_mem_fsm_q;
        x_mem_ready_o        = 1'b0;
        x_mem_result_valid_o = 1'b0;
        x_mem_result_fin     = 1'b0;
        x_mem_result_err     = 1'b0;
        x_mem_load_err       = 1'b0;
        x_mem_store_err      = 1'b0;
        // x_mem_lsu_req        = 1'b0;

        unique case (x_mem_fsm_q)
          MEM_IDLE: begin
            if (x_mem_valid_i & (~x_mem_spec | x_mem_commit)) begin
              if (x_mem_size_err) begin
                x_mem_fsm_d     = MEM_IDLE;
                x_mem_ready_o   = 1'b1;
                x_mem_load_err  = ~x_mem_we;
                x_mem_store_err = x_mem_we;
              end else begin
                x_mem_fsm_d   = MEM_LSU_REQ;
                // x_mem_lsu_req = 1'b1;
                if (lsu_req_done_i) begin
                  x_mem_fsm_d   = MEM_WAIT_RESULT;
                  x_mem_ready_o = 1'b1;
                end
              end
            end
          end
          MEM_LSU_REQ: begin
            // x_mem_lsu_req = 1'b1;
            if (lsu_req_done_i) begin
              x_mem_fsm_d   = MEM_WAIT_RESULT;
              x_mem_ready_o = 1'b1;
            end
          end
          MEM_WAIT_RESULT: begin
            if (lsu_resp_valid_i) begin
              if (x_mem_valid_i & (~x_mem_spec | x_mem_commit)) begin
                if (x_mem_size_err) begin
                  x_mem_fsm_d     = MEM_IDLE;
                  x_mem_ready_o   = 1'b1;
                  x_mem_load_err  = ~x_mem_we;
                  x_mem_store_err = x_mem_we;
                end else begin
                  x_mem_fsm_d   = MEM_LSU_REQ;
                  // x_mem_lsu_req = 1'b1;
                  if (lsu_req_done_i) begin
                    x_mem_fsm_d   = MEM_WAIT_RESULT;
                    x_mem_ready_o = 1'b1;
                  end
                end
              end else begin
                x_mem_fsm_d = MEM_IDLE;
              end
              x_mem_result_valid_o = 1'b1;
              x_mem_result_err     = lsu_load_err_i | lsu_store_err_i | lsu_load_intg_err_i;
              if (x_mem_last_q) begin
                x_mem_result_fin = 1'b1;
              end
            end
          end
          default: begin
            x_mem_fsm_d = MEM_IDLE;
          end
        endcase
      end

      // This code has the same function as the commented code in the state machine above.
      // Make this change because verilator cannot compile the code above.
      logic x_mem_status_idle;
      assign x_mem_status_idle = x_mem_fsm_q == MEM_IDLE |
                                 (x_mem_fsm_q == MEM_WAIT_RESULT & lsu_resp_valid_i);
      assign x_mem_lsu_req = (x_mem_fsm_q == MEM_LSU_REQ) |
                             (x_mem_status_idle & ~x_mem_size_err &
                              x_mem_valid_i & (~x_mem_spec | x_mem_commit));
      assign lsu_x_mem_be_o = x_mem_lsu_req ? x_mem_be : 4'b1111;

      // Only for assertion.
      assign outstanding_xif_load_store_o = (x_mem_fsm_q != MEM_IDLE) | (x_mem_fsm_d != MEM_IDLE);

      // Flip-Flops
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          x_mem_fsm_q <= '0;
        end else begin
          x_mem_fsm_q <= x_mem_fsm_d;
        end
      end

      if (ResetAll) begin : g_x_mem_ra
        always_ff @(posedge clk_i or negedge rst_ni) begin
          if (!rst_ni) begin
            x_mem_last_q <= '0;
            x_mem_id_q   <= '0;
          end else if (x_mem_handshake) begin
            x_mem_last_q <= x_mem_last_d;
            x_mem_id_q   <= x_mem_id_d;
          end
        end
      end else begin : g_x_mem_nr
        always_ff @(posedge clk_i or negedge rst_ni) begin
          if (x_mem_handshake) begin
            x_mem_last_q <= x_mem_last_d;
            x_mem_id_q   <= x_mem_id_d;
          end
        end
      end

    end else begin : gen_no_mem_interface
      // Assign inputs
      logic       unused_x_mem_valid;
      x_mem_req_t unused_x_mem_req;

      assign unused_x_mem_valid = x_mem_valid_i;
      assign unused_x_mem_req   = x_mem_req_i;

      // Zero outputs
      assign x_mem_ready_o        = '0;
      assign x_mem_resp_o         = '0;
      assign x_mem_result_valid_o = '0;
      assign x_mem_result_o       = '0;
      assign x_mem_lsu_req        = 1'b0;

      // Signals from/to scoreboard
      assign x_mem_id_d       = '0;
      assign x_mem_result_fin = '0;
      assign x_mem_result_id  = '0;
      assign x_mem_result_err = 1'b0;

      logic        unused_mem_commit;
      logic [31:0] unused_lsu_rdata;
      assign unused_mem_commit = x_mem_commit;
      assign unused_lsu_rdata  = lsu_rdata_i;

      // LSU signals
      assign lsu_we_o       = lsu_we;
      assign lsu_type_o     = lsu_type;
      assign lsu_sign_ext_o = lsu_sign_ext;
      assign lsu_wdata_o    = rf_rdata_b_fwd;
      assign lsu_x_mem_be_o = 4'b1111;

      // Execution block signals
      assign alu_operand_a_ex_o = alu_operand_a;
      assign alu_operand_b_ex_o = alu_operand_b;

      // LSU privillege level
      assign priv_mode_lsu_xif_o    = '0;
      assign priv_mode_lsu_xif_en_o = 1'b0;

      // Memory interface size error signals
      assign x_mem_load_err  = 1'b0;
      assign x_mem_store_err = 1'b0;

      // Signal only for assertion
      assign outstanding_xif_load_store_o = 1'b0;
    end

    /////////////////
    // SCORE BOARD //
    /////////////////

    // Signal to reset scoreboard and kill requests in issue-commit buffer
    logic  x_exc_err;
    assign x_exc_err = x_result_exc   | x_result_err | x_mem_result_err |
                       x_mem_load_err | x_mem_store_err;

    // Scoreboard registers
    logic [31:0] scoreboard;
    logic [31:1] scoreboard_d, scoreboard_q;
    // Read hazard from xif
    logic        rf_rd_a_hz_xif;
    logic        rf_rd_b_hz_xif;

    // Operand zero always clean.
    assign scoreboard[31:1] = scoreboard_q;
    assign scoreboard[0]    = 1'b0;

    // Validity of register file read
    assign rf_rd_a_hz_xif = scoreboard[rf_raddr_a_o] & ~rf_rd_a_match_xif;
    assign rf_rd_b_hz_xif = scoreboard[rf_raddr_b_o] & ~rf_rd_b_match_xif;

    // The validity of source registers
    assign x_issue_rs_a_valid = ~rf_rd_a_hz_xif & ~stall_ld_a_hz;
    assign x_issue_rs_b_valid = ~rf_rd_b_hz_xif & ~stall_ld_b_hz;

    // Internal signals stalls because of read hazard caused by external instructions
    assign stall_external_rd_hz = instr_valid_i & ~x_issue_candidate &
                                  ((rf_rd_a_hz_xif & rf_ren_a) | (rf_rd_b_hz_xif & rf_ren_b));

    // Set and reset the bits in the scoreboard
    always_comb begin
      scoreboard_d = scoreboard_q;
      if (x_issue_accept & (|rf_waddr_dec)) begin
        scoreboard_d[rf_waddr_dec] = x_issue_wb;
      end
      // If result arrives at the same cycle, overwrite issue
      if (x_result_wb_en & (|x_result_rd)) begin
        scoreboard_d[x_result_rd] = 1'b0;
      end
      if (x_exc_err | wb_exception) begin
        scoreboard_d = '0;
      end
    end

    // Registers for scoreboard
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        scoreboard_q <= '0;
      end else begin
        scoreboard_q <= scoreboard_d;
      end
    end

    /////////////////////////
    // ISSUE-COMMIT BUFFER //
    /////////////////////////

    logic external_exc;

    ibex_xif_issue_commit_buffer issue_commit_buffer_i (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .xif_exception_i(x_exc_err),
      .wb_exception_i (wb_exception),
      .mem_in_wb_i    (outstanding_memory_access),
      .external_exc_o (external_exc),
      .mem_xif_o      (mem_xif),
      .illegal_insn_o (illegal_insn_id),
      // issue interface
      .issue_id_o       (x_issue_id),
      .issue_icb_valid_o(x_issue_icb_valid),
      .issue_valid_i    (x_issue_valid_o),
      .issue_handshake_i(x_issue_handshake),
      .issue_reject_i   (x_issue_reject),
      .issue_exc_i      (x_issue_exc),
      .issue_ls_i       (x_issue_ls),
      // commit interface
      .commit_valid_o(x_commit_valid_o),
      .commit_id_o   (x_commit_id),
      .commit_kill_o (x_commit_kill),
      // memory interface
      .mem_id_i    (x_mem_id_d),
      .mem_commit_o(x_mem_commit),
      // memory result interface
      .mem_result_fin_i(x_mem_result_fin),
      .mem_result_id_i (x_mem_result_id),
      // result interface
      .result_handshake_i(x_result_handshake),
      .result_id_i       (x_result_id)
    );

    assign stall_external_exc = instr_valid_i & ~x_issue_candidate & external_exc;

  end else begin : gen_no_x_interface
    // unused I/Os
    logic [5:0]    unused_ecs_rd;
    logic          unused_x_issue_ready;
    x_issue_resp_t unused_x_issue_resp;
    logic          unused_x_mem_valid;
    x_mem_req_t    unused_x_mem_req;
    logic          unused_x_result_valid;
    x_result_t     unused_x_result;
    logic          unused_x_issue_use_rs3;
    logic          unused_outstanding_memory_access;
    logic [31:0]   unused_lsu_rdata;

    assign unused_ecs_rd         = ecs_rd_i;
    assign unused_x_issue_ready  = x_issue_ready_i;
    assign unused_x_issue_resp   = x_issue_resp_i;
    assign unused_x_mem_valid    = x_mem_valid_i;
    assign unused_x_mem_req      = x_mem_req_i;
    assign unused_x_result_valid = x_result_valid_i;
    assign unused_x_result       = x_result_i;
    assign unused_lsu_rdata      = lsu_rdata_i;

    assign unused_x_issue_use_rs3           = x_issue_use_rs3;
    assign unused_outstanding_memory_access = outstanding_memory_access;

    assign ecs_wr_o               = '0;
    assign ecs_wen_o              = '0;
    assign x_issue_valid_o        = 1'b0;
    assign x_issue_req_o          = '0;
    assign x_commit_valid_o       = 1'b0;
    assign x_commit_o             = '0;
    assign x_result_ready_o       = 1'b0;
    assign x_mem_ready_o          = 1'b0;
    assign x_mem_resp_o           = '0;
    assign x_mem_result_valid_o   = 1'b0;
    assign x_mem_result_o         = '0;
    assign priv_mode_lsu_xif_o    = '0;
    assign priv_mode_lsu_xif_en_o = 1'b0;
    assign outstanding_xif_load_store_o = 1'b0;

    // X-Interface signals that needs to be set to 0
    assign x_issue_candidate    = 1'b0;
    assign x_issue_get_rs3      = 1'b0;
    assign x_issue_accept       = 1'b0;
    assign stall_offl           = 1'b0;
    assign stall_external_exc   = 1'b0;
    assign stall_external_rd_hz = 1'b0;
    assign imd_val_we_x_issue   = 1'b0;
    assign x_result_wb_en       = 1'b0;
    assign x_result_exc         = 1'b0;
    assign x_result_exccode     = '0;
    assign x_result_err         = 1'b0;
    assign x_mem_load_err       = 1'b0;
    assign x_mem_store_err      = 1'b0;
    assign x_mem_lsu_req        = 1'b0;

    // wire connections
    assign illegal_insn_id    = illegal_insn_dec | illegal_csr_insn_i;
    assign rf_waddr_id_o      = rf_waddr_dec;
    assign rf_wdata_id_o      = rf_wdata_mux;
    assign lsu_we_o           = lsu_we;
    assign lsu_type_o         = lsu_type;
    assign lsu_sign_ext_o     = lsu_sign_ext;
    assign lsu_wdata_o        = rf_rdata_b_fwd;
    assign lsu_x_mem_be_o     = 4'b1111;
    assign alu_operand_a_ex_o = alu_operand_a;
    assign alu_operand_b_ex_o = alu_operand_b;
  end

  //////////
  // FCOV //
  //////////

  `DV_FCOV_SIGNAL_GEN_IF(logic, rf_rd_wb_hz,
    (gen_stall_mem.rf_rd_a_hz | gen_stall_mem.rf_rd_b_hz) & instr_valid_i, WritebackStage)
  `DV_FCOV_SIGNAL(logic, branch_taken,
    instr_executing & (id_fsm_q == FIRST_CYCLE) & branch_decision_i)
  `DV_FCOV_SIGNAL(logic, branch_not_taken,
    instr_executing & (id_fsm_q == FIRST_CYCLE) & ~branch_decision_i)

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT_KNOWN_IF(IbexAluOpMuxSelKnown, alu_op_a_mux_sel, instr_valid_i)
  `ASSERT(IbexAluAOpMuxSelValid, instr_valid_i |-> alu_op_a_mux_sel inside {
      OP_A_REG_A,
      OP_A_FWD,
      OP_A_CURRPC,
      OP_A_IMM})
  `ASSERT_KNOWN_IF(IbexBTAluAOpMuxSelKnown, bt_a_mux_sel, instr_valid_i)
  `ASSERT(IbexBTAluAOpMuxSelValid, instr_valid_i |-> bt_a_mux_sel inside {
      OP_A_REG_A,
      OP_A_CURRPC})
  `ASSERT_KNOWN_IF(IbexBTAluBOpMuxSelKnown, bt_b_mux_sel, instr_valid_i)
  `ASSERT(IbexBTAluBOpMuxSelValid, instr_valid_i |-> bt_b_mux_sel inside {
      IMM_B_I,
      IMM_B_B,
      IMM_B_J,
      IMM_B_INCR_PC})
  `ASSERT(IbexRegfileWdataSelValid, instr_valid_i |-> rf_wdata_sel inside {
      RF_WD_EX,
      RF_WD_CSR})
  `ASSERT_KNOWN(IbexWbStateKnown, id_fsm_q)

  // Branch decision must be valid when jumping.
  `ASSERT_KNOWN_IF(IbexBranchDecisionValid, branch_decision_i,
      instr_valid_i && !(illegal_csr_insn_i || instr_fetch_err_i))

  // Instruction delivered to ID stage can not contain X.
  `ASSERT_KNOWN_IF(IbexIdInstrKnown, instr_rdata_i,
      instr_valid_i && !(illegal_c_insn_i || instr_fetch_err_i))

  // Instruction delivered to ID stage can not contain X.
  `ASSERT_KNOWN_IF(IbexIdInstrALUKnown, instr_rdata_alu_i,
      instr_valid_i && !(illegal_c_insn_i || instr_fetch_err_i))

  // Multicycle enable signals must be unique.
  `ASSERT(IbexMulticycleEnableUnique,
      $onehot0({lsu_req_dec, multdiv_en_dec, branch_in_dec, jump_in_dec}))

  // Multicycle stage register enable must be unique.
  `ASSERT(IbexMulticycleStageRegEnableUnique,
      $onehot0({|imd_val_we_ex_i, imd_val_we_x_issue}))

  // LSU enable must be unique.
  `ASSERT(LoadStoreUnitEnableUnique,
      $onehot0({x_mem_lsu_req, lsu_req}))

  // Duplicated instruction flops must match
  // === as DV environment can produce instructions with Xs in, so must use precise match that
  // includes Xs
  `ASSERT(IbexDuplicateInstrMatch, instr_valid_i |-> instr_rdata_i === instr_rdata_alu_i)

  `ifdef CHECK_MISALIGNED
  `ASSERT(IbexMisalignedMemoryAccess, !lsu_addr_incr_req_i)
  `endif

endmodule
