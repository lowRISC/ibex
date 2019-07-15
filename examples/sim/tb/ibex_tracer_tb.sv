// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Sample testbench for Ibex tracer
// The `nop` instruction is the only input

module ibex_tracer_tb;
  logic         clk         = 1'b0;
  logic         rst_n       = 1'b0;
  logic [31:0]  instr_rdata = 32'h00000013;
  logic [31:0]  data_rdata  = 32'h00000000;

  initial begin: clock_gen
    forever begin
      #5ns clk = 1'b0;
      #5ns clk = 1'b1;
    end
  end

  initial begin: reset_gen
    rst_n = 1'b0;
    #160ns rst_n = 1'b1;
    #400ns $finish;
  end

  initial begin: instr_gen
    #200ns instr_rdata = 32'h00000013;
    #10ns instr_rdata = 32'h00000093;
    #10ns instr_rdata = 32'h00400113;
    #10ns instr_rdata = 32'hff810113;
    #10ns instr_rdata = 32'h13410d13;
    #10ns instr_rdata = 32'he1070713;
    #10ns instr_rdata = 32'hfff7c793;
    #10ns instr_rdata = 32'h00000013;
    #10ns instr_rdata = 32'h002d2c23;
    #10ns instr_rdata = 32'h00000013;
    #10ns instr_rdata = 32'h000d2083;
          data_rdata  = 32'h22222222;
    #10ns instr_rdata = 32'h60008113;
    #10ns instr_rdata = 32'h00000013;
    #10ns instr_rdata = 32'h00000113;
    #30ns instr_rdata = 32'h00000013;
    #10ns instr_rdata = 32'h0000000f;
    #10ns instr_rdata = 32'h00000013;
    #10ns instr_rdata = 32'h00000013;
    #10ns instr_rdata = 32'h0000000f;
  end

  ibex_core_tracer ibex_i (
    .clk_i                  (clk),
    .rst_ni                 (rst_n),

    .test_en_i              (1'b0),

    // Core ID, Cluster ID and boot address are considered more or less static
    .core_id_i              (4'b0),
    .cluster_id_i           (6'b0),
    .boot_addr_i            (32'b0),

    // Instruction memory interface
    .instr_req_o            (),
    .instr_gnt_i            (instr_gnt),
    .instr_rvalid_i         (instr_rvalid),
    .instr_addr_o           (),
    .instr_rdata_i          (instr_rdata),

    // Data memory interface
    .data_req_o             (),
    .data_gnt_i             (1'b1),
    .data_rvalid_i          (1'b1),
    .data_we_o              (),
    .data_be_o              (),
    .data_addr_o            (),
    .data_wdata_o           (),
    .data_rdata_i           (data_rdata),
    .data_err_i             (1'b0),

    // Interrupt inputs
    .irq_i                  (1'b0),
    .irq_id_i               (5'b0),
    .irq_ack_o              (),
    .irq_id_o               (),

    // Debug Interface
    .debug_req_i            (1'b0),

    // RISC-V Formal Interface
    .rvfi_valid             (),
    .rvfi_order             (),
    .rvfi_insn              (),
    .rvfi_insn_uncompressed (),
    .rvfi_trap              (),
    .rvfi_halt              (),
    .rvfi_intr              (),
    .rvfi_mode              (),
    .rvfi_rs1_addr          (),
    .rvfi_rs2_addr          (),
    .rvfi_rs1_rdata         (),
    .rvfi_rs2_rdata         (),
    .rvfi_rd_addr           (),
    .rvfi_rd_wdata          (),
    .rvfi_pc_rdata          (),
    .rvfi_pc_wdata          (),
    .rvfi_mem_addr          (),
    .rvfi_mem_rmask         (),
    .rvfi_mem_wmask         (),
    .rvfi_mem_rdata         (),
    .rvfi_mem_wdata         (),

    // CPU Control Signals
    .fetch_enable_i         (1'b1)
  );

endmodule
