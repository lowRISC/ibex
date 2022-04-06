// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

interface core_ibex_pmp_fcov_if import ibex_pkg::*; #(
    parameter bit          PMPEnable      = 1'b0,
    // Granularity of NAPOT access,
    // 0 = No restriction, 1 = 8 byte, 2 = 16 byte, 3 = 32 byte, etc.
    parameter int unsigned PMPGranularity = 0,
    // Number of implemented regions
    parameter int unsigned PMPNumRegions  = 4
) (
  input clk_i,
  input rst_ni,

  input ibex_pkg::pmp_cfg_t  csr_pmp_cfg     [PMPNumRegions],
  input logic                pmp_req_err     [3],
  input pmp_mseccfg_t        csr_pmp_mseccfg,

  input logic data_req_out,

  input logic lsu_req_done
);
  localparam int unsigned PMPNumChan = 3;

  `include "dv_fcov_macros.svh"
  import uvm_pkg::*;

  // Enum to give more readable coverage results for privilege bits. 4 bits are from the pmpcfg CSF
  // (L, X, W, R) and the 5th is the MML bit. Setting the MML bit changes the meaning of the other
  // 4 bits
  // TODO: Better MML names?
  typedef enum logic [4:0] {
    PMP_PRIV_NONE     = 5'b00000,
    PMP_PRIV_R        = 5'b00001,
    PMP_PRIV_W        = 5'b00010,
    PMP_PRIV_WR       = 5'b00011,
    PMP_PRIV_X        = 5'b00100,
    PMP_PRIV_XR       = 5'b00101,
    PMP_PRIV_XW       = 5'b00110,
    PMP_PRIV_XWR      = 5'b00111,
    PMP_PRIV_L        = 5'b01000,
    PMP_PRIV_LR       = 5'b01001,
    PMP_PRIV_LW       = 5'b01010,
    PMP_PRIV_LWR      = 5'b01011,
    PMP_PRIV_LX       = 5'b01100,
    PMP_PRIV_LXR      = 5'b01101,
    PMP_PRIV_LXW      = 5'b01110,
    PMP_PRIV_LXWR     = 5'b01111,
    PMP_PRIV_MML_NONE = 5'b10000,
    PMP_PRIV_MML_R    = 5'b10001,
    PMP_PRIV_MML_W    = 5'b10010,
    PMP_PRIV_MML_WR   = 5'b10011,
    PMP_PRIV_MML_X    = 5'b10100,
    PMP_PRIV_MML_XR   = 5'b10101,
    PMP_PRIV_MML_XW   = 5'b10110,
    PMP_PRIV_MML_XWR  = 5'b10111,
    PMP_PRIV_MML_L    = 5'b11000,
    PMP_PRIV_MML_LR   = 5'b11001,
    PMP_PRIV_MML_LW   = 5'b11010,
    PMP_PRIV_MML_LWR  = 5'b11011,
    PMP_PRIV_MML_LX   = 5'b11100,
    PMP_PRIV_MML_LXR  = 5'b11101,
    PMP_PRIV_MML_LXW  = 5'b11110,
    PMP_PRIV_MML_LXWR = 5'b11111
  } pmp_priv_bits_e;

  // Break out PMP signals into individually named signals for direct use in `cross` as it cannot
  // deal with hierarchical references or unpacked arrays.
  logic pmp_iside_req_err;
  logic pmp_iside2_req_err;
  logic pmp_dside_req_err;

  assign pmp_iside_req_err  = pmp_req_err[PMP_I];
  assign pmp_iside2_req_err = pmp_req_err[PMP_I2];
  assign pmp_dside_req_err  = pmp_req_err[PMP_D];

  logic [PMPNumRegions-1:0] current_priv_perm_check;
  bit en_pmp_fcov;

  initial begin
    if (PMPEnable) begin
      void'($value$plusargs("enable_ibex_fcov=%d", en_pmp_fcov));
    end else begin
      en_pmp_fcov = 1'b0;
    end
  end

  if (PMPEnable) begin : g_pmp_cgs
    for (genvar i_region = 0; i_region < PMPNumRegions; i_region += 1) begin : g_pmp_region_fcov
      pmp_priv_bits_e pmp_region_priv_bits;

      assign pmp_region_priv_bits = pmp_priv_bits_e'({csr_pmp_mseccfg.mml,
                                                      csr_pmp_cfg[i_region].lock,
                                                      csr_pmp_cfg[i_region].exec,
                                                      csr_pmp_cfg[i_region].write,
                                                      csr_pmp_cfg[i_region].read});
      // Do the permission check for Data channel with the privilege level from Instruction channels.
      // This way we can check the effect of mstatus.mprv changing privilege levels for LSU related
      // operations.
      assign current_priv_perm_check[i_region] =
        g_pmp.pmp_i.perm_check_wrapper(csr_pmp_mseccfg.mml,
                                       csr_pmp_cfg[i_region],
                                       g_pmp.pmp_i.pmp_req_type_i[PMP_D],
                                       cs_registers_i.priv_mode_id_o,
                                       g_pmp.pmp_i.region_basic_perm_check[PMP_D][i_region]);

      covergroup pmp_region_cg @(posedge clk_i);
        option.per_instance = 1;
        option.name = "pmp_region_cg";

        cp_warl_check_pmpcfg : coverpoint
          g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_warl_check_pmpcfg;

        cp_region_mode : coverpoint csr_pmp_cfg[i_region].mode;

        cp_region_priv_bits : coverpoint pmp_region_priv_bits {
          wildcard ignore_bins ignore = {5'b1????};
          wildcard illegal_bins illegal = {5'b0??10};
        }

        cp_priv_lvl_iside : coverpoint g_pmp.pmp_priv_lvl[PMP_I] {
          illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
        }

        cp_req_type_iside : coverpoint g_pmp.pmp_req_type[PMP_I] {
          illegal_bins illegal = {PMP_ACC_WRITE, PMP_ACC_READ};
        }

        cp_priv_lvl_iside2 : coverpoint g_pmp.pmp_priv_lvl[PMP_I2] {
          illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
        }

        cp_req_type_iside2 : coverpoint g_pmp.pmp_req_type[PMP_I2] {
          illegal_bins illegal = {PMP_ACC_WRITE, PMP_ACC_READ};
        }

        cp_priv_lvl_dside : coverpoint g_pmp.pmp_priv_lvl[PMP_D] {
          illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
        }

        cp_req_type_dside : coverpoint g_pmp.pmp_req_type[PMP_D] {
          illegal_bins illegal = {PMP_ACC_EXEC};
        }

        pmp_iside_mode_cross : cross cp_region_mode, pmp_iside_req_err
          iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan_access);

        pmp_iside2_mode_cross : cross cp_region_mode, pmp_iside2_req_err
          iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan2_access);

        pmp_dside_mode_cross : cross cp_region_mode, pmp_dside_req_err
          iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_dchan_access);

        // TODO: Coverage for accesses that don't match any regions

        pmp_iside_priv_bits_cross :
          cross cp_region_priv_bits, cp_req_type_iside, cp_priv_lvl_iside, pmp_iside_req_err
            iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan_access &&
                 g_pmp_fcov_signals.fcov_pmp_region_ichan_priority[i_region]                 &&
                 csr_pmp_cfg[i_region].mode != PMP_MODE_OFF) {

          // Will never see a succesful exec access when execute is disallowed
          illegal_bins illegal_allow_exec = (binsof(cp_region_priv_bits) intersect {5'b00000,
            5'b00001, 5'b00010, 5'b00011, 5'b01000, 5'b01001, 5'b01010, 5'b01011} &&
            binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
            binsof(pmp_iside_req_err) intersect {0}) with (cp_priv_lvl_iside == PRIV_LVL_U ||
                                                           (cp_region_priv_bits & 5'b01000));

          // Will never see an exec access denied when executed is allowed
          illegal_bins illegal_deny_exec = binsof(cp_region_priv_bits) intersect {5'b00100, 5'b00101,
            5'b00110, 5'b00111, 5'b01100, 5'b01101, 5'b01110, 5'b01111} &&
            binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
            binsof(pmp_iside_req_err) intersect {1};
        }

        pmp_iside2_priv_bits_cross :
          cross cp_region_priv_bits, cp_req_type_iside2, cp_priv_lvl_iside2, pmp_iside2_req_err
            iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan2_access &&
                 g_pmp_fcov_signals.fcov_pmp_region_ichan2_priority[i_region]                 &&
                 csr_pmp_cfg[i_region].mode != PMP_MODE_OFF) {

          // Will never see a succesful exec access when execute is disallowed
          illegal_bins illegal_allow_exec = (binsof(cp_region_priv_bits) intersect {5'b00000,
            5'b00001, 5'b00010, 5'b00011, 5'b01000, 5'b01001, 5'b01010, 5'b01011} &&
            binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
            binsof(pmp_iside2_req_err) intersect {0}) with (cp_priv_lvl_iside2 == PRIV_LVL_U ||
                                                           (cp_region_priv_bits & 5'b01000));

          // Will never see an exec access denied when execute is allowed
          illegal_bins illegal_deny_exec = binsof(cp_region_priv_bits) intersect {5'b00100, 5'b00101,
            5'b00110, 5'b00111, 5'b01100, 5'b01101, 5'b01110, 5'b01111} &&
            binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
            binsof(pmp_iside2_req_err) intersect {1};
        }

        pmp_dside_priv_bits_cross :
          cross cp_region_priv_bits, cp_req_type_dside, cp_priv_lvl_dside, pmp_dside_req_err
            iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_dchan_access &&
                 g_pmp_fcov_signals.fcov_pmp_region_dchan_priority[i_region]                 &&
                 csr_pmp_cfg[i_region].mode != PMP_MODE_OFF) {

          // Will never see a succesful read access when read is disallowed
          illegal_bins illegal_allow_read = (binsof(cp_region_priv_bits) intersect {5'b00000,
            5'b00010, 5'b00100, 5'b00110, 5'b01000, 5'b01010, 5'b01100, 5'b01110} &&
            binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
            binsof(pmp_dside_req_err) intersect {0}) with (cp_priv_lvl_dside == PRIV_LVL_U ||
                                                           (cp_region_priv_bits & 5'b01000));

          // Will never see a read access denied when read is allowed
          illegal_bins illegal_deny_read = binsof(cp_region_priv_bits) intersect {5'b00001, 5'b00011,
            5'b00101, 5'b00111, 5'b01001, 5'b01011, 5'b01101, 5'b01111} &&
            binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
            binsof(pmp_dside_req_err) intersect {1};

          // Will never see a succesful write access when write is disallowed
          illegal_bins illegal_allow_write = (binsof(cp_region_priv_bits) intersect {5'b00000,
            5'b00001, 5'b00100, 5'b00101, 5'b01000, 5'b01001, 5'b01100, 5'b01101} &&
            binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
            binsof(pmp_dside_req_err) intersect {0}) with (cp_priv_lvl_dside == PRIV_LVL_U ||
                                                           (cp_region_priv_bits & 5'b01000));

          // Will never see a write access denied when write is allowed
          illegal_bins illegal_deny_write = binsof(cp_region_priv_bits) intersect {5'b00010, 5'b00011,
            5'b00110, 5'b00111, 5'b01010, 5'b01011, 5'b01110, 5'b01111} &&
            binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
            binsof(pmp_dside_req_err) intersect {1};
        }
      endgroup

      `DV_FCOV_INSTANTIATE_CG(pmp_region_cg, en_pmp_fcov)
    end

    // Current Priv means the privilege level of Instruction channels and Ibex in general. Note that
    // the privilege level of PMP data channel can be set something different than this using MSTATUS.MPRV
    // and MSTATUS.MPP.
    logic pmp_current_priv_req_err;
    assign pmp_current_priv_req_err =
      g_pmp.pmp_i.access_fault_check(csr_pmp_mseccfg.mmwp,
                                     g_pmp.pmp_i.region_match_all[PMP_D],
                                     cs_registers_i.priv_mode_id_o,
                                     current_priv_perm_check);

    covergroup pmp_top_cg @(posedge clk_i);
      option.per_instance = 1;
      option.name = "pmp_top_cg";

      cp_pmp_iside_region_override :
        coverpoint g_pmp.pmp_i.g_access_check[PMP_I].fcov_pmp_region_override
          iff (if_stage_i.if_id_pipe_reg_we);

      cp_pmp_iside2_region_override :
        coverpoint g_pmp.pmp_i.g_access_check[PMP_I2].fcov_pmp_region_override
          iff (if_stage_i.if_id_pipe_reg_we);

      cp_pmp_dside_region_override :
        coverpoint g_pmp.pmp_i.g_access_check[PMP_D].fcov_pmp_region_override iff (data_req_out);

      cp_mprv: coverpoint cs_registers_i.mstatus_q.mprv;

      mprv_effect_cross: cross cp_mprv, cs_registers_i.mstatus_q.mpp,
                               cs_registers_i.priv_mode_id_o, pmp_current_priv_req_err,
                               pmp_dside_req_err iff
                                 (id_stage_i.instr_rdata_i[6:0] inside
                                    {ibex_pkg::OPCODE_LOAD, ibex_pkg::OPCODE_STORE}){
        // If MPRV is set to 0, system priv lvl and lsu priv lvl has to be same.
        illegal_bins illegal_mprv =
          binsof(cp_mprv) intersect {1'b0} with (pmp_current_priv_req_err != pmp_dside_req_err);
        // Ibex does not support H or S mode.
        ignore_bins unsupported_priv_lvl =
          binsof(cs_registers_i.mstatus_q.mpp) intersect {PRIV_LVL_H, PRIV_LVL_S} ||
          binsof(cs_registers_i.priv_mode_id_o) intersect {PRIV_LVL_H, PRIV_LVL_S};
      }
    endgroup

    `DV_FCOV_INSTANTIATE_CG(pmp_top_cg, en_pmp_fcov)
  end

endinterface
