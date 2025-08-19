// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 *
 * This register file is designed to make FPGA synthesis tools infer RAM primitives. For Xilinx
 * FPGA architectures, it will produce RAM32M primitives. Other vendors have not yet been tested.
 */
module ibex_register_file_fpga #(
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
  input  logic [          4:0] raddr_a_i,
  output logic [DataWidth-1:0] rdata_a_o,
  //Read port R2
  input  logic [          4:0] raddr_b_i,
  output logic [DataWidth-1:0] rdata_b_o,
  // Write port W1
  input  logic [          4:0] waddr_a_i,
  input  logic [DataWidth-1:0] wdata_a_i,
  input  logic                 we_a_i,

  // This indicates whether spurious WE or non-one-hot encoded raddr are detected.
  output logic                 err_o
);

  localparam int ADDR_WIDTH = RV32E ? 4 : 5;
  localparam int NUM_WORDS = 2 ** ADDR_WIDTH;

  logic [DataWidth-1:0] mem[NUM_WORDS];
  logic we; // write enable if writing to any register other than R0

  // Encode we_a/raddr_a/raddr_b into one-hot encoded signals
  logic [NUM_WORDS-1:0] raddr_onehot_a, raddr_onehot_b, we_onehot_a;

  // WE strobe and one-hot encoded raddr alert.
  logic oh_raddr_a_err, oh_raddr_b_err, oh_we_err;

  logic [DataWidth-1:0] mem_o_a, mem_o_b;

  // Common security functionality
  ibex_register_file_common #(
    .FPGA(1),
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

  if (RdataMuxCheck) begin : gen_rdata_mux_check
    // MUX register to rdata_a/b_o according to raddr_a/b_onehot.
    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_rdata_a_mux (
      .clk_i,
      .rst_ni,
      .in_i  (mem),
      .sel_i (raddr_onehot_a),
      .out_o (mem_o_a)
    );

    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_rdata_b_mux (
      .clk_i,
      .rst_ni,
      .in_i  (mem),
      .sel_i (raddr_onehot_b),
      .out_o (mem_o_b)
    );

    assign rdata_a_o = (raddr_a_i == '0) ? WordZeroVal : mem_o_a;
    assign rdata_b_o = (raddr_b_i == '0) ? WordZeroVal : mem_o_b;
  end else begin : gen_no_rdata_mux_check
    assign rdata_a_o = (raddr_a_i == '0) ? WordZeroVal : mem[raddr_a_i];
    assign rdata_b_o = (raddr_b_i == '0) ? WordZeroVal : mem[raddr_b_i];

    logic unused_raddr_onehot, unused_oh_raddr_err;
    assign unused_raddr_onehot = ^{raddr_onehot_a, raddr_onehot_b};
    assign unused_oh_raddr_err = ^{oh_raddr_a_err, oh_raddr_b_err};
  end

  // we select
  assign we = (waddr_a_i == '0) ? 1'b0 : we_onehot_a[0];

  // Note that the SystemVerilog LRM requires variables on the LHS of assignments within
  // "always_ff" to not be written to by any other process. However, to enable the initialization
  // of the inferred RAM32M primitives with non-zero values, below "initial" procedure is needed.
  // Therefore, we use "always" instead of the generally preferred "always_ff" for the synchronous
  // write procedure.
  always @(posedge clk_i) begin : sync_write
    if (we == 1'b1) begin
      mem[waddr_a_i] <= wdata_a_i;
    end
  end : sync_write

  // Make sure we initialize the BRAM with the correct register reset value.
  initial begin
    for (int k = 0; k < NUM_WORDS; k++) begin
      mem[k] = WordZeroVal;
    end
  end

  // Reset not used in this register file version
  logic unused_rst_ni;
  assign unused_rst_ni = rst_ni;

  // Dummy instruction changes not relevant for FPGA implementation
  logic unused_dummy_instr;
  assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;
  // Test enable signal not used in FPGA implementation
  logic unused_test_en;
  assign unused_test_en = test_en_i;

  if (WrenCheck) begin : gen_wren_check
  end else begin : gen_no_wren_check
    logic unused_oh_we_err;
    assign unused_oh_we_err = oh_we_err;  // this is never read from in this case
  end

endmodule
