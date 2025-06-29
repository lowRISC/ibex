// Copyleft 2025 ISOLDE
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Fetch variable length instruction
 *
 * Decodes RISC-V variable lenght encoded instructions 
 */

`include "axi/typedef.svh"

/// Protocol adapter which translates memory requests to the AXI4 protocol.
///
/// This module acts like an SRAM and makes AXI4 requests downstream.
///
/// Supports multiple outstanding requests and will have responses for reads **and** writes.
/// Response latency is not fixed and for sure **not 1** and depends on the AXI4 memory system.
/// The `mem_rsp_valid_o` can have multiple cycles of latency from the corresponding `mem_gnt_o`.

module isolde_tcdm_to_axi #(
    /// Memory request address width.
    parameter int unsigned    MemAddrWidth = 32'd32,
    /// AXI4-Lite address width.
    parameter int unsigned    AxiAddrWidth = 32'd32,
    /// Data width in bit of the memory request data **and** the Axi4-Lite data channels.
    parameter int unsigned    DataWidth    = 32'd32,
    /// How many requests can be in flight at the same time. (Depth of the response mux FIFO).
    parameter int unsigned    MaxRequests  = 32'd1,
    /// Protection signal the module should emit on the AXI4 transactions.
    parameter axi_pkg::prot_t AxiProt      = 3'b000,
    /// AXI4 request struct definition.
    parameter type            axi_req_t    = logic,
    /// AXI4 response struct definition.
    parameter type            axi_rsp_t    = logic
) (
    /// Clock input, positive edge triggered.
    input  logic                clk_i,
    /// Asynchronous reset, active low.
    input  logic                rst_ni,
    /// Memory slave port request
           isolde_tcdm_if.slave s_tcdm,
    /// AXI4 master port, slave aw cache signal
    input  axi_pkg::cache_t     slv_aw_cache_i,
    /// AXI4 master port, slave ar cache signal
    input  axi_pkg::cache_t     slv_ar_cache_i,
    /// AXI4 master port, request output.
    output axi_req_t            axi_req_o,
    /// AXI4 master port, response input.
    input  axi_rsp_t            axi_rsp_i
);

  axi_from_mem #(
      .MemAddrWidth(MemAddrWidth),
      .AxiAddrWidth(AxiAddrWidth),
      .DataWidth   (DataWidth),
      .MaxRequests (MaxRequests),
      .AxiProt     (AxiProt),
      .axi_req_t   (axi_req_t),
      .axi_rsp_t   (axi_rsp_t)
  ) i_tdcm_to_axi_bridge (
      .clk_i,
      .rst_ni,
      .mem_req_i      (s_tcdm.req.req),
      .mem_addr_i     (s_tcdm.req.addr),
      .mem_we_i       (s_tcdm.req.we),
      .mem_wdata_i    (s_tcdm.req.data),
      .mem_be_i       (s_tcdm.req.be),
      .mem_gnt_o      (s_tcdm.rsp.gnt),
      .mem_rsp_valid_o(s_tcdm.rsp.valid),
      .mem_rsp_rdata_o(s_tcdm.rsp.data),
      .mem_rsp_error_o(s_tcdm.rsp.err),
      .slv_aw_cache_i ('0),
      .slv_ar_cache_i ('0),
      .axi_req_o      (axi_req_o),
      .axi_rsp_i      (axi_rsp_i)
  );

endmodule
