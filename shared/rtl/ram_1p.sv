// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Single-port RAM with 1 cycle read/write delay, 32 bit words
 */

`include "prim_assert.sv"

module ram_1p #(
    parameter int Depth = 128
) (
    input               clk_i,
    input               rst_ni,

    input               req_i,
    input               we_i,
    input        [ 3:0] be_i,
    input        [31:0] addr_i,
    input        [31:0] wdata_i,
    output logic        rvalid_o,
    output logic [31:0] rdata_o
);

  localparam int Aw = $clog2(Depth);

  logic [Aw-1:0] addr_idx;
  assign addr_idx = addr_i[Aw-1+2:2];
  logic [31-Aw:0] unused_addr_parts;
  assign unused_addr_parts = {addr_i[31:Aw+2], addr_i[1:0]};

  // Convert byte mask to SRAM bit mask.
  logic [31:0] wmask;
  always_comb begin
    for (int i = 0 ; i < 4 ; i++) begin
      // mask for read data
      wmask[8*i+:8] = {8{be_i[i]}};
    end
  end

  // |rvalid| in the bus module is an "ack", while prim_ram_1p associates the
  // meaning "returned read data is valid" with this signal.
  // Convert the RAM meaning to the meaning assumed by the bus module.
  logic read_valid, we_q;
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      we_q <= 1'b0;
    end else begin
      we_q <= we_i;
    end
  end
  assign rvalid_o = read_valid | we_q;

  prim_generic_ram_1p #(
      .Width(32),
      .DataBitsPerMask(8),
      .Depth(Depth)
    ) u_ram (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .req_i     (req_i),
      .write_i   (we_i),
      .wmask_i   (wmask),
      .addr_i    (addr_idx),
      .wdata_i   (wdata_i),
      .rvalid_o  (read_valid),
      .rdata_o   (rdata_o)
    );
endmodule
