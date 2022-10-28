// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to probe DUT internal signal
interface core_ibex_dut_probe_if(input logic clk);

  import uvm_pkg::*;

  logic                    reset;
  logic                    illegal_instr;
  logic                    ecall;
  logic                    wfi;
  logic                    ebreak;
  logic                    dret;
  logic                    mret;
  ibex_pkg::ibex_mubi_t    fetch_enable;
  logic                    core_sleep;
  logic                    alert_minor;
  logic                    alert_major_internal;
  logic                    alert_major_bus;
  logic                    debug_req;
  ibex_pkg::priv_lvl_e     priv_mode;
  ibex_pkg::ctrl_fsm_e     ctrl_fsm_cs;
  logic                    debug_mode;
  logic                    double_fault_seen;
  logic                    rf_ren_a;
  logic                    rf_ren_b;
  logic                    rf_rd_a_wb_match;
  logic                    rf_rd_b_wb_match;

  clocking dut_cb @(posedge clk);
    output fetch_enable;
    output debug_req;
    input reset;
    input illegal_instr;
    input ecall;
    input wfi;
    input ebreak;
    input dret;
    input mret;
    input core_sleep;
    input alert_minor;
    input alert_major_internal;
    input alert_major_bus;
    input priv_mode;
    input ctrl_fsm_cs;
    input debug_mode;
    input double_fault_seen;
    input rf_ren_a;
    input rf_ren_b;
    input rf_rd_a_wb_match;
    input rf_rd_b_wb_match;
  endclocking

  initial begin
    debug_req = 1'b0;
  end

  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_rf_ren_a, rf_ren_a)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_rf_ren_b, rf_ren_b)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_rf_rd_a_wb_match, rf_rd_a_wb_match)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_rf_rd_b_wb_match, rf_rd_b_wb_match)

endinterface
