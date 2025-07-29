// Copyleft ISOLDE 2025

/*
 * Inspired by Heterogeneous Cluster Interconnect (HCI)
 * See: https://github.com/pulp-platform/hci
 * 
 * The core master connected to s_tcdm_core has higher prio over the hardware engine(hwe)
 */

module isolde_hci_interconnect #(
    parameter bit ALIGN = 1'b0,
    parameter int unsigned ALIGNMENT = 64,  // Address alignment boundary in bytes
    parameter int unsigned HCI_DW = 288,  // Data width of hci interface
    //
    parameter int unsigned N_TCDM_BANKS = HCI_DW / 32  // Number of Memory banks
) (
    input logic clk_i,  // Clock input, positive edge triggered
    input logic rst_ni,  // Asynchronous reset, active low
    hci_core_intf.slave s_hci_core,  // hwe slave interface
    isolde_tcdm_if.slave s_tcdm_core,  // core slave interface, higher prio
    output isolde_tcdm_pkg::req_t mem_req_o[N_TCDM_BANKS:0],
    input isolde_tcdm_pkg::rsp_t mem_rsp_i[N_TCDM_BANKS:0]


);

  //

  logic [N_TCDM_BANKS-1:0] tcdm_gnt;
  logic [N_TCDM_BANKS-1:0][31:0] tcdm_r_data;
  logic [N_TCDM_BANKS-1:0] tcdm_r_valid;

  // Aligned address computation
  logic [isolde_tcdm_pkg::CORE_AW-1:0] aligned_addr;

  always_comb begin
    if (ALIGN) aligned_addr = s_hci_core.add + (s_hci_core.add % ALIGNMENT);
    else aligned_addr = s_hci_core.add;
  end

  // === HCI binding ===
  for (genvar ii = 0; ii < N_TCDM_BANKS; ii++) begin : hci_binding

    ///
    assign mem_req_o[ii].req  = s_tcdm_core.req.req ? 0 : s_hci_core.req;
    assign mem_req_o[ii].addr = aligned_addr + ii * 4;
    assign mem_req_o[ii].we   = ~s_hci_core.wen;
    assign mem_req_o[ii].be   = s_hci_core.be[(ii+1)*4-1:ii*4];
    assign mem_req_o[ii].data = s_hci_core.data[(ii+1)*32-1:ii*32];
    ///
    assign tcdm_gnt[ii]       = mem_rsp_i[ii].gnt;
    assign tcdm_r_valid[ii]   = mem_rsp_i[ii].valid;
    assign tcdm_r_data[ii]    = mem_rsp_i[ii].data;

  end

  assign s_hci_core.gnt = &tcdm_gnt;
  assign s_hci_core.r_data = {tcdm_r_data};
  assign s_hci_core.r_valid = &tcdm_r_valid;
  assign s_hci_core.r_opc = '0;
  assign s_hci_core.r_user = '0;
  //
  assign mem_req_o[N_TCDM_BANKS] = s_tcdm_core.req;
  assign s_tcdm_core.rsp = mem_rsp_i[N_TCDM_BANKS];


endmodule
