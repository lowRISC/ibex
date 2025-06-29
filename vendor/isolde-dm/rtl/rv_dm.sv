// Copyleft 2025  ISOLDE

// Top-level debug module (DM)
//
// This module implements the RISC-V debug specification version 0.13,
//
// This toplevel wraps the PULP debug module available from
// https://github.com/pulp-platform/riscv-dbg

module rv_dm
  import rv_dm_pkg::*;
#(

    parameter logic [31:0] IdcodeValue = 32'h249511C3
) (
    input logic clk_i,  // clock
    input logic rst_ni,  // asynchronous reset active low, connect PoR
                         // here, not the system reset
    input logic [31:0] next_dm_addr_i,  // static word address of the next debug module.
    /// DMI slave port 
    isolde_tcdm_if.slave s_dmi,
    /// System Bus master port
    isolde_tcdm_if.master m_sbus,
    /// JTAG
    input jtag_pkg::jtag_req_t jtag_in,
    output jtag_pkg::jtag_rsp_t jtag_out,
    output logic [NrHarts-1:0] debug_req_o,
    output logic dmactive_o,  // debug module is active
    input logic [NrHarts-1:0] unavailable_i  // communicate whether the hart is unavailable
    // (e.g.: power down)
);
  // static debug hartinfo
  localparam dm::hartinfo_t DebugHartInfo = '{
      zero1: '0,
      nscratch: 2,  // Debug module needs at least two scratch regs
      zero0: 0,
      dataaccess: 1'b1,  // data registers are memory mapped in the debugger
      datasize: dm::DataCount,
      dataaddr: dm::DataAddr
  };


  logic dmi_en;
  assign dmi_en = 1'b1;  //to do read a pin configuration


  dm::dmi_req_t dmi_req;
  dm::dmi_resp_t dmi_rsp;
  logic dmi_rst_n;
  logic dmi_req_valid_raw, dmi_rsp_ready_raw;
  logic dmi_req_valid, dmi_req_ready;
  logic dmi_rsp_valid, dmi_rsp_ready;
  // Gated DMI signals
  assign dmi_req_valid = dmi_req_valid_raw & dmi_en;
  assign dmi_rsp_ready = dmi_rsp_ready_raw & dmi_en;

  dm::hartinfo_t [NrHarts-1:0] hartinfo;
  for (genvar i = 0; i < NrHarts; i++) begin : gen_dm_hart_ctrl
    assign hartinfo[i] = DebugHartInfo;
  end
  localparam int BusWidth = 32;
  // all harts have contiguous IDs
  localparam logic [NrHarts-1:0] SelectableHarts = {NrHarts{1'b1}};

  //logic [NrHarts-1:0] debug_req_en;
  logic [NrHarts-1:0] debug_req;
  // for (genvar i = 0; i < NrHarts; i++) begin : gen_debug_req_hart
  //   // SEC_CM: DM_EN.CTRL.LC_GATED
  //   assign debug_req_en[i] = lc_tx_test_true_strict(lc_hw_debug_en_gated[LcEnDebugReq + i]);
  // end

  ////////////////////////
  // NDM Reset Tracking //
  ////////////////////////

  logic reset_req_en;
  logic ndmreset_req, ndmreset_ack;
  logic ndmreset_req_qual;
  // SEC_CM: DM_EN.CTRL.LC_GATED
  assign reset_req_en   = 1'b1;  //TODO read a pin configuration
  assign ndmreset_req_o = ndmreset_req_qual & reset_req_en;

  // Sample the processor reset to detect lc reset assertion.
  logic lc_rst_asserted_async;
  prim_flop_2sync #(
      .Width(1),
      .ResetValue(1)  // Resets to 1 to indicate assertion.
  ) u_prim_flop_2sync_lc_rst_assert (
      .clk_i,  // Use RV_DM clock
      .rst_ni(rst_lc_ni),  // Use LC reset here that resets the entire system except the RV_DM.
      .d_i(1'b0),  // Set to 0 to indicate deassertion.
      .q_o(lc_rst_asserted_async)
  );

  // Note that the output of the above flops can be metastable at reset assertion, since the reset
  // signal is coming from a different clock domain and has not been synchronized with clk_i.
  logic lc_rst_asserted;
  prim_flop_2sync #(
      .Width(1)
  ) u_prim_flop_2sync_lc_rst_sync (
      .clk_i,
      .rst_ni,
      .d_i(lc_rst_asserted_async),
      .q_o(lc_rst_asserted)
  );

  // The acknowledgement pulse sets the dmstatus.allhavereset / dmstatus.anyhavereset registers in
  // RV_DM. It should only be asserted once an NDM reset request has been fully completed.
  logic ndmreset_pending_q;
  logic lc_rst_pending_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_ndm_reset
    if (!rst_ni) begin
      ndmreset_pending_q <= 1'b0;
      lc_rst_pending_q   <= 1'b0;
    end else begin
      // Only set this if there was no previous pending NDM request.
      if (ndmreset_req && !ndmreset_pending_q) begin
        ndmreset_pending_q <= 1'b1;
      end else if (ndmreset_ack && ndmreset_pending_q) begin
        ndmreset_pending_q <= 1'b0;
      end
      // We only track lc resets that are asserted during an active ndm reset request..
      if (ndmreset_pending_q && lc_rst_asserted) begin
        lc_rst_pending_q <= 1'b1;
      end else if (ndmreset_ack && lc_rst_pending_q) begin
        lc_rst_pending_q <= 1'b0;
      end
    end
  end

  // In order to ACK the following conditions must be met
  // 1) an NDM reset request was asserted and is pending
  // 2) a lc reset was asserted after the NDM reset request
  // 3) the NDM reset request was deasserted
  // 4) the NDM lc request was deasserted
  // 5) the debug module has been ungated for operation (depending on LC state, OTP config and CSR)
  assign ndmreset_ack = ndmreset_pending_q &&
                        lc_rst_pending_q &&
                        !ndmreset_req &&
                        !lc_rst_asserted &&
                        reset_req_en;

  logic testmode;
  assign testmode = 1'b0;

  ///////////////////////////
  // Debug Module Instance //
  ///////////////////////////


  isolde_tcdm_if dm_top_dgb_req ();

  assign dm_top_dgb_req.req = s_dmi.req;
  assign s_dmi.rsp          = dm_top_dgb_req.rsp;
  

  //logic [31:0]   slave_rdata_test;
  dm_top #(
      .NrHarts        (NrHarts),
      .BusWidth       (BusWidth),
      .SelectableHarts(SelectableHarts),
      // The debug module provides a simplified ROM for systems that map the debug ROM to offset 0x0
      // on the system bus. In that case, only one scratch register has to be implemented in the core.
      // However, we require that the DM can be placed at arbitrary offsets in the system, which
      // requires the generalized debug ROM implementation and two scratch registers. We hence set
      // this parameter to a non-zero value (inside dm_mem, this just feeds into a comparison with 0).
      .DmBaseAddress  (1)
  ) i_dm_top (
      .clk_i,
      .rst_ni,
      .next_dm_addr_i,
      .testmode_i    (testmode),
      .ndmreset_o    (ndmreset_req),
      .ndmreset_ack_i(ndmreset_ack),
      .dmactive_o,
      .debug_req_o,
      .unavailable_i,
      .hartinfo_i    (hartinfo),
      // debug request 
      .slave_req_i   (dm_top_dgb_req.req.req),
      .slave_we_i    (dm_top_dgb_req.req.we),
      .slave_addr_i  (dm_top_dgb_req.req.addr),
      .slave_be_i    (dm_top_dgb_req.req.be),
      .slave_wdata_i (dm_top_dgb_req.req.data),
      .slave_rdata_o (dm_top_dgb_req.rsp.data),
      .slave_err_o     (dm_top_dgb_req.rsp.err),
      .slave_gnt_o     (dm_top_dgb_req.rsp.gnt),
      .slave_valid_o   (dm_top_dgb_req.rsp.valid),
      //.slave_rdata_o   (slave_rdata_test),


      // System Bus access
      .master_req_o    (m_sbus.req.req),
      .master_add_o    (m_sbus.req.addr),
      .master_we_o     (m_sbus.req.we),
      .master_wdata_o  (m_sbus.req.data),
      .master_be_o     (m_sbus.req.be),
      .master_gnt_i    (m_sbus.rsp.gnt),
      .master_r_valid_i(m_sbus.rsp.valid),
      .master_r_err_i  (m_sbus.rsp.err),
      //.master_r_other_err_i  (host_r_other_err    ),
      .master_r_rdata_i(m_sbus.rsp.data),
      //  DMI -> DM
      .dmi_rst_ni      (dmi_rst_n),
      .dmi_req_valid_i (dmi_req_valid),
      .dmi_req_ready_o (dmi_req_ready),
      .dmi_req_i       (dmi_req),
      .dmi_resp_valid_o(dmi_rsp_valid),
      .dmi_resp_ready_i(dmi_rsp_ready),
      .dmi_resp_o      (dmi_rsp)
  );

  // JTAG TAP
  dmi_jtag #(
      .IdcodeValue(IdcodeValue)
      //.NumDmiWordAbits(7)
  ) i_dmi_jtag (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .testmode_i(testmode),
      //.test_rst_ni      (scan_rst_ni),

      .dmi_rst_no     (dmi_rst_n),
      .dmi_req_o      (dmi_req),
      .dmi_req_valid_o(dmi_req_valid_raw),
      .dmi_req_ready_i(dmi_req_ready & dmi_en),

      .dmi_resp_i      (dmi_rsp),
      .dmi_resp_ready_o(dmi_rsp_ready_raw),
      .dmi_resp_valid_i(dmi_rsp_valid & dmi_en),

      //JTAG
      .tck_i   (jtag_in.tck),
      .tms_i   (jtag_in.tms),
      .trst_ni (jtag_in.trst_n),
      .td_i    (jtag_in.tdi),
      .td_o    (jtag_out.tdo),
      .tdo_oe_o(jtag_out.tdo_oe)
  );
endmodule
