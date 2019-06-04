// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module core_ibex_tb_top;

  import uvm_pkg::*;

  logic clk;
  logic rst_n;
  logic fetch_enable;

  clk_if ibex_clk_if(.clk(clk));

  // TODO(taliu) Resolve the tied-off ports
  ibex_core dut(
    .clk_i(clk),
    .rst_ni(rst_n),
    .test_en_i(1'b1),
    .core_id_i('0),
    .cluster_id_i('0),
    .boot_addr_i(`BOOT_ADDR), // align with spike boot address
    .irq_i('0),
    .irq_id_i('0),
    .debug_req_i('0),
    .fetch_enable_i(fetch_enable)
  );

  ibex_mem_intf data_mem_vif();
  ibex_mem_intf instr_mem_vif();

  initial begin
    //data load/store vif connection
    force data_mem_vif.clock    = clk;
    force data_mem_vif.reset    = ~rst_n;
    force data_mem_vif.request  = dut.data_req_o;
    force dut.data_gnt_i        = data_mem_vif.grant;
    force dut.data_rvalid_i     = data_mem_vif.rvalid;
    force data_mem_vif.we       = dut.data_we_o;
    force data_mem_vif.be       = dut.data_be_o;
    force data_mem_vif.addr     = dut.data_addr_o;
    force data_mem_vif.wdata    = dut.data_wdata_o;
    force dut.data_rdata_i      = data_mem_vif.rdata;
    force dut.data_err_i        = 0; // TODO(taliu) Support interface error
    //instruction fetch vif connnection
    force instr_mem_vif.clock   = clk;
    force instr_mem_vif.reset   = ~rst_n;
    force instr_mem_vif.request = dut.instr_req_o;
    force dut.instr_gnt_i       = instr_mem_vif.grant;
    force instr_mem_vif.we      = 0;
    force instr_mem_vif.be      = 0;
    force instr_mem_vif.wdata   = 0;
    force dut.instr_rvalid_i    = instr_mem_vif.rvalid;
    force instr_mem_vif.addr    = dut.instr_addr_o;
    force dut.instr_rdata_i     = instr_mem_vif.rdata;
  end

  // DUT probe interface
  core_ibex_dut_probe_if dut_if(.clk(clk));
  assign dut_if.ecall = dut.id_stage_i.ecall_insn_dec;
  assign fetch_enable = dut_if.fetch_enable;

  initial begin
    uvm_config_db#(virtual clk_if)::set(null, "*", "clk_if", ibex_clk_if);
    uvm_config_db#(virtual core_ibex_dut_probe_if)::set(null, "*", "dut_if", dut_if);
    uvm_config_db#(virtual ibex_mem_intf)::set(null, "*data_if_slave*", "vif", data_mem_vif);
    uvm_config_db#(virtual ibex_mem_intf)::set(null, "*instr_if_slave*", "vif", instr_mem_vif);
    run_test();
  end

  // Generate clk
  initial begin
    clk = 1'b0;
    forever begin
      #10 clk = ~clk;
    end
  end

  // Generate reset
  initial begin
    rst_n = 1'b0;
    repeat(100) @(posedge clk);
    rst_n = 1'b1;
  end

endmodule
