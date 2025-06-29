// Copyleft 2025 ISOLDE 
// Copyright (c) 2020 ETH Zurich and University of Bologna
// SPDX-License-Identifier: SHL-0.51
//
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Samuel Riedel <sriedel@iis.ee.ethz.ch>
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

`include "axi/typedef.svh"

/// Infinite (Simulation-Only) Memory with AXI Slave Port
///
/// The memory array is named `mem`, and it is *not* initialized or reset.  This makes it possible to
/// load the memory of this module in simulation with an external `$readmem*` command, e.g.,
/// ```sv
/// axi_sim_mem #( ... ) i_sim_mem ( ... );
/// initial begin
///   $readmemh("file_with_memory_addrs_and_data.mem", i_sim_mem.memory);
///   $readmemh("file_with_memory_addrs_and_read_errors.mem", i_sim_mem.rerr);
///   $readmemh("file_with_memory_addrs_and_write_errors.mem", i_sim_mem.werr);
/// end
/// ```
/// `memory` is addressed (or indexed) byte-wise with `AddrWidth`-wide addresses.
///
/// This module does not support atomic operations (ATOPs).
module isolde_axi_sim_mem #(
    /// AXI Address Width
    parameter int unsigned AddrWidth = 32'd32,
    /// AXI Data Width
    parameter int unsigned DataWidth = 32'd32,
    /// AXI ID Width
    parameter int unsigned IdWidth = 32'd0,
    /// AXI User Width.
    parameter int unsigned UserWidth = 32'd0,
    /// Number of request ports
    parameter int unsigned NumPorts = 32'd1,
    /// Size of the memory (default 1024 entries)
    parameter MEMORY_SIZE = 1024,
    /// AXI4 request struct definition
    parameter type axi_req_t = logic,
    /// AXI4 response struct definition
    parameter type axi_rsp_t = logic,
    /// Warn on accesses to uninitialized bytes
    parameter bit WarnUninitialized = 1'b0,
    /// Default value for uninitialized memory (undefined, zeros, ones, random)
    parameter UninitializedData = "undefined",
    /// Clear error on access
    parameter bit ClearErrOnAccess = 1'b0,
    /// Application delay (measured after rising clock edge)
    parameter time ApplDelay = 0ps,
    /// Acquisition delay (measured after rising clock edge)
    parameter time AcqDelay = 0ps
) (
    /// Rising-edge clock
    input  logic                    clk_i,
    /// Active-low reset
    input  logic                    rst_ni,
    /// AXI4 request struct
    input  axi_req_t [NumPorts-1:0] axi_req_i,
    /// AXI4 response struct
    output axi_rsp_t [NumPorts-1:0] axi_rsp_o

);

  logic mem_busy;
  logic from_axi_atop;
  hwpe_stream_intf_tcdm to_mem_tcdm[0:0] (.clk(clk_i));
  isolde_tcdm_if from_axi();

  always_comb begin : bind_mem
    to_mem_tcdm[0].req = from_axi.req.req;
    to_mem_tcdm[0].wen = ~from_axi.req.we;
    to_mem_tcdm[0].be = from_axi.req.be;
    to_mem_tcdm[0].add = from_axi.req.addr;
    to_mem_tcdm[0].data = from_axi.req.data;
    //
    from_axi.rsp.gnt = to_mem_tcdm[0].gnt;
    from_axi.rsp.valid = to_mem_tcdm[0].r_valid;
    from_axi.rsp.data = to_mem_tcdm[0].r_data;
    from_axi.rsp.err = 1'b0;  //to_mem_tcdm.
  end

  axi_to_mem #(
      .axi_req_t   (axi_req_t),
      .axi_resp_t  (axi_rsp_t),
      .AddrWidth   (AddrWidth),
      .DataWidth   (DataWidth),
      .IdWidth     (IdWidth),
      .NumBanks    (1),
      .BufDepth    (1),
      .HideStrb    (1),
      .OutFifoDepth(1)
  ) i_axi_to_mem (
      .clk_i,
      .rst_ni,
      .busy_o(mem_busy),
      .axi_req_i(axi_req_i),
      .axi_resp_o(axi_rsp_o),
      .mem_req_o(from_axi.req.req),
      .mem_gnt_i(from_axi.rsp.gnt),
      .mem_addr_o(from_axi.req.addr),
      .mem_wdata_o(from_axi.req.data),
      .mem_strb_o(from_axi.req.be),
      .mem_atop_o(from_axi_atop),
      .mem_we_o(from_axi.req.we),
      .mem_rvalid_i(from_axi.rsp.valid),
      .mem_rdata_i(from_axi.rsp.data)
  );


  tb_tcdm_verilator #(
      .MP          (1),
      .MEMORY_SIZE (MEMORY_SIZE),
      .BASE_ADDR   (0),
      .DELAY_CYCLES(0)
  ) i_mem (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .enable_i(1'b1),
      .tcdm    (to_mem_tcdm)
  );

endmodule
