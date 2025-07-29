// Copyleft 2024 ISOLDE
// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Yvan Tortorella <yvan.tortorella@unibo.it>
//

module isolde_redmule_top
  //import cv32e40x_pkg::*;
  //import fpnew_pkg::*;
  //import hci_package::*;
 // import redmule_pkg::*;
  //import hwpe_ctrl_package::*;
  //import hwpe_stream_package::*;
#(
    parameter int unsigned ID_WIDTH = 8,
    parameter int unsigned N_CORES = 8,
    // TCDM port dimension (in bits)
    parameter int unsigned DW = DATA_W,
    parameter int unsigned AddrWidth = 32,
    // Number of PEs within a row
    localparam int unsigned Height = ARRAY_HEIGHT,
    // Number of parallel rows
    localparam int unsigned Width = ARRAY_WIDTH
    // Number of bits for the given format
) (
    input  logic                    clk_i,
    input  logic                    rst_ni,
    input  logic                    test_mode_i,
    input  logic                    fetch_enable_i,
    // evnets
    output logic [N_CORES-1:0][1:0] evt_o,

    hci_core_intf.master m_hci_core,
`ifdef TARGET_REDMULE_COMPLEX
    isolde_cv_x_if       core_xif
`elsif TARGET_REDMULE_HWPE
    isolde_tcdm_if.slave s_tcdm_ctrl
`endif
);

  localparam int unsigned SysDataWidth = 32;
  localparam int unsigned SysInstWidth = 32;

  logic busy;
  logic s_clk, s_clk_en;

`ifdef TARGET_REDMULE_HWPE
  hwpe_ctrl_intf_periph periph (.clk(clk_i));

  always_comb begin : bind_periph
    periph.req = s_tcdm_ctrl.req.req;
    periph.add = s_tcdm_ctrl.req.addr;
    periph.wen = ~s_tcdm_ctrl.req.we;
    periph.be = s_tcdm_ctrl.req.be;
    periph.data = s_tcdm_ctrl.req.data;
    periph.id = '0;
    //periph_r_valid = '0;
    //
    s_tcdm_ctrl.rsp.gnt = periph.gnt;
    s_tcdm_ctrl.rsp.valid = periph.r_valid;
    s_tcdm_ctrl.rsp.err = '0;
    s_tcdm_ctrl.rsp.data = periph.r_data;
  end
`endif


  always_ff @(posedge clk_i or negedge rst_ni) begin : clock_enable
    if (~rst_ni) s_clk_en <= 1'b0;
    else s_clk_en <= fetch_enable_i;
  end

  tc_clk_gating sys_clock_gating (
      .clk_i    (clk_i),
      .en_i     (s_clk_en),
      .test_en_i(test_mode_i),
      .clk_o    (s_clk)
  );

  redmule_top #(
      .ID_WIDTH    (ID_WIDTH),
      .N_CORES     (1),
      .DW          (DW),
      .X_EXT       (1'b1),
      .SysInstWidth(SysInstWidth),
      .SysDataWidth(SysDataWidth)
  ) i_redmule_top (
      .clk_i              (s_clk),
      .rst_ni             (rst_ni),
      .test_mode_i        (test_mode_i),
      .evt_o              (evt_o),
      .busy_o             (busy),
      .tcdm               (m_hci_core),
`ifdef TARGET_REDMULE_COMPLEX
      .xif_issue_if_i     (core_xif.coproc_issue),
      .xif_result_if_o    (core_xif.coproc_result),
      .xif_compressed_if_i(core_xif.coproc_compressed),
      .xif_mem_if_o       (core_xif.coproc_mem)
`elsif TARGET_REDMULE_HWPE
      .periph             (periph)
`endif
  );

endmodule : isolde_redmule_top
