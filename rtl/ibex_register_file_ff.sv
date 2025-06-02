// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 * This register file is based on flip flops. Use this register file when
 * targeting FPGA synthesis or Verilator simulation.
 */
module ibex_register_file_ff #(
  parameter bit                   RV32E             = 0,
  parameter int unsigned          DataWidth         = 32,
  parameter bit                   DummyInstructions = 0,
  parameter bit                   WrenCheck         = 0,
  parameter bit                   RdataMuxCheck     = 0,
  parameter logic [DataWidth-1:0] WordZeroVal       = '0
) (
  // Clock and Reset
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  logic                 test_en_i,
  input  logic                 dummy_instr_id_i,
  input  logic                 dummy_instr_wb_i,

  //Read port R1
  input  logic [4:0]           raddr_a_i,
  output logic [DataWidth-1:0] rdata_a_o,

  //Read port R2
  input  logic [4:0]           raddr_b_i,
  output logic [DataWidth-1:0] rdata_b_o,


  // Write port W1
  input  logic [4:0]           waddr_a_i,
  input  logic [DataWidth-1:0] wdata_a_i,
  input  logic                 we_a_i,

  // This indicates whether spurious WE or non-one-hot encoded raddr are detected.
  output logic                 err_o
);

  localparam int unsigned ADDR_WIDTH = RV32E ? 4 : 5;
  localparam int unsigned NUM_WORDS  = 2**ADDR_WIDTH;

  logic [DataWidth-1:0] rf_reg   [NUM_WORDS];

  // Encode we_a/raddr_a/raddr_b into one-hot encoded signals
  logic [NUM_WORDS-1:0] raddr_onehot_a, raddr_onehot_b, we_onehot_a;

  // One-hot encoding error signals
  logic oh_raddr_a_err, oh_raddr_b_err, oh_we_err;

  // Common security functionality
  ibex_register_file_common #(
    .AddrWidth(ADDR_WIDTH),
    .NumWords(NUM_WORDS),
    .WrenCheck(WrenCheck),
    .RdataMuxCheck(RdataMuxCheck)
  ) security_module (
    .clk_i,
    .rst_ni,
    .raddr_a_i,
    .raddr_onehot_a,
    .oh_raddr_a_err,
    .raddr_b_i,
    .raddr_onehot_b,
    .oh_raddr_b_err,
    .waddr_a_i,
    .we_a_i,
    .we_onehot_a,
    .oh_we_err,
    .err_o
  );

  // No flops for R0 as it's hard-wired to 0
  for (genvar i = 1; i < NUM_WORDS; i++) begin : g_rf_flops
    logic [DataWidth-1:0] rf_reg_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q <= WordZeroVal;
      end else if (we_onehot_a[i]) begin
        rf_reg_q <= wdata_a_i;
      end
    end

    assign rf_reg[i] = rf_reg_q;
  end

  // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
  // real instructions.
  if (DummyInstructions) begin : g_dummy_r0
    // SEC_CM: CTRL_FLOW.UNPREDICTABLE
    logic                 we_r0_dummy;
    logic [DataWidth-1:0] rf_r0_q;

    // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
    assign we_r0_dummy = we_a_i & dummy_instr_wb_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_r0_q <= WordZeroVal;
      end else if (we_r0_dummy) begin
        rf_r0_q <= wdata_a_i;
      end
    end

    // Output the dummy data for dummy instructions, otherwise R0 reads as zero
    assign rf_reg[0] = dummy_instr_id_i ? rf_r0_q : WordZeroVal;

  end else begin : g_normal_r0
    logic unused_dummy_instr;
    assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;

    // R0 is nil
    assign rf_reg[0] = WordZeroVal;
  end

  if (RdataMuxCheck) begin : gen_rdata_mux_check
    // MUX register to rdata_a/b_o according to raddr_a/b_onehot.
    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_rdata_a_mux (
      .clk_i,
      .rst_ni,
      .in_i  (rf_reg),
      .sel_i (raddr_onehot_a),
      .out_o (rdata_a_o)
    );

    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_rdata_b_mux (
      .clk_i,
      .rst_ni,
      .in_i  (rf_reg),
      .sel_i (raddr_onehot_b),
      .out_o (rdata_b_o)
    );
  end else begin : gen_no_rdata_mux_check
    assign rdata_a_o = rf_reg[raddr_a_i];
    assign rdata_b_o = rf_reg[raddr_b_i];

    logic unused_raddr_onehot, unused_oh_raddr_err;
    assign unused_raddr_onehot = ^{raddr_onehot_a, raddr_onehot_b};
    assign unused_oh_raddr_err = ^{oh_raddr_a_err, oh_raddr_b_err};
  end

  // Signal not used in FF register file
  logic unused_test_en;
  assign unused_test_en = test_en_i;

  if (WrenCheck) begin : gen_wren_check
  end else begin : gen_no_wren_check
    logic unused_strobe, unused_oh_we_err;
    assign unused_strobe = we_onehot_a[0];  // this is never read from in this case
    assign unused_oh_we_err = oh_we_err;  // this is never read from in this case
  end

endmodule
