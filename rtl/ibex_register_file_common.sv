// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file common security functionality across multiple implementations
 * - Contains common security hardening logic across implementations
 * - Contains checks for onehot encoding of addresses and write enable(s)
 */

module ibex_register_file_common #(
  parameter bit          FPGA          = 0,
  parameter int unsigned AddrWidth     = 5,
  parameter int unsigned NumWords      = 2 ** AddrWidth,
  parameter bit          WrenCheck     = 0,
  parameter bit          RdataMuxCheck = 0
) (
  /* verilator lint_off UNUSED */
  // Clock and Reset
  input  logic                clk_i,
  input  logic                rst_ni,
  /* verilator lint_on UNUSED */

  //Read port R1
  input  logic [4:0]          raddr_a_i,
  output logic [NumWords-1:0] raddr_onehot_a,
  output logic                oh_raddr_a_err,

  //Read port R2
  input  logic [4:0]          raddr_b_i,
  output logic [NumWords-1:0] raddr_onehot_b,
  output logic                oh_raddr_b_err,

  // Write port W1
  input  logic [4:0]          waddr_a_i,
  input  logic                we_a_i,
  output logic [NumWords-1:0] we_onehot_a,
  output logic                oh_we_err,

  // This indicates whether spurious WE or non-one-hot encoded raddr are detected.
  output logic                err_o
);

  if (FPGA) begin : gen_fpga_oh_we_a_o_decoder
    always_comb begin : oh_we_a_o_decoder
      for (int unsigned i = 0; i < NumWords; i++) begin
        we_onehot_a[i] = (i == 0) ? we_a_i : 1'b0;
      end
    end
  end else begin : gen_other_oh_we_a_o_decoder
    always_comb begin : oh_we_a_o_decoder
      for (int unsigned i = 0; i < NumWords; i++) begin
        we_onehot_a[i] = (waddr_a_i == 5'(i)) ? we_a_i : 1'b0;
      end
    end
  end

  // SEC_CM: DATA_REG_SW.GLITCH_DETECT
  // This checks for spurious WE strobes on the regfile.
  if (WrenCheck) begin : gen_wren_check
    // Buffer the decoded write enable bits so that the checker
    // is not optimized into the address decoding logic.
    logic [NumWords-1:0] we_onehot_a_buf;
    prim_buf #(
      .Width(NumWords)
    ) u_prim_buf (
      .in_i (we_onehot_a),
      .out_o(we_onehot_a_buf)
    );

    prim_onehot_check #(
      .AddrWidth  (AddrWidth),
      .OneHotWidth(NumWords),
      .AddrCheck  (FPGA ? 0 : 1),  // disable in case of FPGA impl, as we use [0] only
      .EnableCheck(1),
    ) u_prim_onehot_check (
      .clk_i,
      .rst_ni,
      .oh_i  (we_onehot_a_buf),
      .addr_i(waddr_a_i),
      .en_i  (we_a_i),
      .err_o (oh_we_err)
    );
  end else begin : gen_no_wren_check
    if (FPGA) begin : gen_unused_wren_check
      logic unused_waddr_a;
      assign unused_waddr_a = ^waddr_a_i;
    end
    assign oh_we_err = 1'b0;
  end

  if (RdataMuxCheck) begin : gen_rdata_mux_check
    // Encode raddr_a/b into one-hot encoded signals.
    logic [NumWords-1:0] raddr_onehot_a_buf, raddr_onehot_b_buf;
    prim_onehot_enc #(
      .OneHotWidth(NumWords)
    ) u_prim_onehot_enc_raddr_a (
      .in_i (raddr_a_i),
      .en_i (1'b1),
      .out_o(raddr_onehot_a)
    );

    prim_onehot_enc #(
      .OneHotWidth(NumWords)
    ) u_prim_onehot_enc_raddr_b (
      .in_i (raddr_b_i),
      .en_i (1'b1),
      .out_o(raddr_onehot_b)
    );

    // Buffer the one-hot encoded signals so that the checkers
    // are not optimized.
    prim_buf #(
      .Width(NumWords)
    ) u_prim_buf_raddr_a (
      .in_i (raddr_onehot_a),
      .out_o(raddr_onehot_a_buf)
    );

    prim_buf #(
      .Width(NumWords)
    ) u_prim_buf_raddr_b (
      .in_i (raddr_onehot_b),
      .out_o(raddr_onehot_b_buf)
    );

    // SEC_CM: DATA_REG_SW.GLITCH_DETECT
    // Check the one-hot encoded signals for glitches.
    prim_onehot_check #(
      .AddrWidth  (AddrWidth),
      .OneHotWidth(NumWords),
      .AddrCheck  (1),
      // When AddrCheck=1 also EnableCheck needs to be 1.
      .EnableCheck(1)
    ) u_prim_onehot_check_raddr_a (
      .clk_i,
      .rst_ni,
      .oh_i  (raddr_onehot_a_buf),
      .addr_i(raddr_a_i),
      // Set enable=1 as address is always valid.
      .en_i  (1'b1),
      .err_o (oh_raddr_a_err)
    );

    prim_onehot_check #(
      .AddrWidth  (AddrWidth),
      .OneHotWidth(NumWords),
      .AddrCheck  (1),
      // When AddrCheck=1 also EnableCheck needs to be 1.
      .EnableCheck(1)
    ) u_prim_onehot_check_raddr_b (
      .clk_i,
      .rst_ni,
      .oh_i  (raddr_onehot_b_buf),
      .addr_i(raddr_b_i),
      // Set enable=1 as address is always valid.
      .en_i  (1'b1),
      .err_o (oh_raddr_b_err)
    );
  end else begin : gen_no_rdata_mux_check
    assign oh_raddr_a_err = 1'b0;
    assign oh_raddr_b_err = 1'b0;
    assign raddr_onehot_a = '0;
    assign raddr_onehot_b = '0;

    logic unused_raddr;
    assign unused_raddr = ^{raddr_a_i, raddr_b_i};
  end

  assign err_o = oh_raddr_a_err || oh_raddr_b_err || oh_we_err;

endmodule
