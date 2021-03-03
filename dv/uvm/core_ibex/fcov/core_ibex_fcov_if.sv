// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface core_ibex_fcov_if import ibex_pkg::*; (
  input clk_i,
  input rst_ni,

  input priv_lvl_e priv_mode_id,
  input priv_lvl_e priv_mode_if,
  input priv_lvl_e priv_mode_lsu
);
  `include "dv_fcov_macros.svh"
  import uvm_pkg::*;

  typedef enum {
    InsnCategoryALU,
    InsnCategoryMult,
    InsnCategoryDiv,
    InsnCategoryBranch,
    InsnCategoryJump,
    InsnCategoryLoad,
    InsnCategoryStore,
    InsnCategoryOther,
    InsnCategoryNone
  } insn_category_e;

  typedef enum {
    IdStallTypeNone,
    IdStallTypeInsn,
    IdStallTypeLdHz,
    IdStallTypeMem
  } id_stall_type_e;

  insn_category_e id_instr_category;

  // Set `id_instr_category` to the appropriate category for the uncompressed instruction in the
  // ID/EX stage.  Compressed instructions are not handled (`id_stage_i.instr_rdata_i` is always
  // uncompressed).  When the `id_stage.instr_valid_i` isn't set `InsnCategoryNone` is the given
  // instruction category.
  // TODO: Illegal instructions
  always_comb begin
    case (id_stage_i.instr_rdata_i[6:0])
      ibex_pkg::OPCODE_LUI:    id_instr_category = InsnCategoryALU;
      ibex_pkg::OPCODE_AUIPC:  id_instr_category = InsnCategoryALU;
      ibex_pkg::OPCODE_JAL:    id_instr_category = InsnCategoryJump;
      ibex_pkg::OPCODE_JALR:   id_instr_category = InsnCategoryJump;
      ibex_pkg::OPCODE_BRANCH: id_instr_category = InsnCategoryBranch;
      ibex_pkg::OPCODE_LOAD:   id_instr_category = InsnCategoryLoad;
      ibex_pkg::OPCODE_STORE:  id_instr_category = InsnCategoryStore;
      ibex_pkg::OPCODE_OP_IMM: id_instr_category = InsnCategoryALU;
      ibex_pkg::OPCODE_OP: begin
        if(id_stage_i.instr_rdata_i[31:25] == 7'b0000000) begin
          id_instr_category = InsnCategoryALU; // RV32I ALU reg-reg ops
        end else if (id_stage_i.instr_rdata_i[31:25] == 7'b0000001) begin
          if (id_stage_i.instr_rdata_i[14]) begin
            id_instr_category = InsnCategoryMult; //MUL*
          end else begin
            id_instr_category = InsnCategoryDiv; // DIV*
          end
        end
      end
      default: id_instr_category = InsnCategoryOther;
    endcase

    if (!id_stage_i.instr_valid_i) begin
      id_instr_category = InsnCategoryNone;
    end
  end

  id_stall_type_e id_stall_type;

  // Set `id_stall_type` to the appropriate type based on signals in the ID/EX stage
  always_comb begin
    id_stall_type = IdStallTypeNone;

    if (id_stage_i.instr_valid_i) begin
      if (id_stage_i.stall_mem) begin
        id_stall_type = IdStallTypeMem;
      end

      if (id_stage_i.stall_ld_hz) begin
        id_stall_type = IdStallTypeLdHz;
      end

      if (id_stage_i.stall_multdiv || id_stage_i.stall_branch ||
          id_stage_i.stall_jump) begin
        id_stall_type = IdStallTypeInsn;
      end
    end
  end

  `DV_FCOV_SVA(instruction_unstalled, id_stall_type != IdStallTypeNone ##1
                                      id_stall_type == IdStallTypeNone)

  covergroup uarch_cg @(posedge clk_i);
    type_option.strobe = 1;

    `DV_FCOV_EXPR_SEEN(insn_unstalled, instruction_unstalled.triggered)

    cp_insn_category_id: coverpoint id_instr_category;

    cp_stall_type_id: coverpoint id_stall_type;

    cp_wb_reg_hz: coverpoint id_stage_i.fcov_rf_rd_wb_hz;
    cp_wb_load_hz: coverpoint id_stage_i.fcov_rf_rd_wb_hz &&
                              wb_stage_i.outstanding_load_wb_o;

    cp_ls_error_exception: coverpoint load_store_unit_i.fcov_ls_error_exception;
    cp_ls_pmp_exception: coverpoint load_store_unit_i.fcov_ls_pmp_exception;

    cp_branch_taken: coverpoint id_stage_i.fcov_branch_taken;
    cp_branch_not_taken: coverpoint id_stage_i.fcov_branch_not_taken;

    cp_priv_mode_id: coverpoint priv_mode_id;
    cp_priv_mode_if: coverpoint priv_mode_if;
    cp_prov_mode_lsu: coverpoint priv_mode_lsu;

    `DV_FCOV_EXPR_SEEN(interrupt_taken, id_stage_i.controller_i.fcov_interrupt_taken)
    `DV_FCOV_EXPR_SEEN(debug_entry_if, id_stage_i.controller_i.fcov_debug_entry_if)
    `DV_FCOV_EXPR_SEEN(debug_entry_id, id_stage_i.controller_i.fcov_debug_entry_id)
    `DV_FCOV_EXPR_SEEN(pipe_flush, id_stage_i.controller_i.fcov_pipe_flush)

    wb_reg_hz_instr_cross: cross cp_insn_category_id, cp_wb_reg_hz;
    stall_cross: cross cp_insn_category_id, cp_stall_type_id;
    pipe_cross: cross cp_insn_category_id, if_stage_i.if_instr_valid,
                      wb_stage_i.fcov_wb_valid;

    interrupt_taken_instr_cross: cross cp_insn_unstalled, cp_interrupt_taken, cp_insn_category_id;
    debug_entry_if_instr_cross: cross cp_debug_entry_if, cp_insn_category_id;
    pipe_flush_instr_cross: cross cp_pipe_flush, cp_insn_category_id;
  endgroup

  bit en_uarch_cov;

  initial begin
   void'($value$plusargs("enable_uarch_cov=%d", en_uarch_cov));
  end

  `DV_FCOV_INSTANTIATE_CG(uarch_cg, en_uarch_cov)
endinterface
