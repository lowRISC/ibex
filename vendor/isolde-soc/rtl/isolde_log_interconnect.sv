// Copyleft ISOLDE 2025

/* this is inspired from the hci_log_interconnect.sv file from https://github.com/pulp-platform/hci.git
 * original authors:
 * Francesco Conti <f.conti@unibo.it>
 *
 * Low-order memory interleaving interconnect
 * Address: A = [row bits | bank bits | offset bits]
 *
    Offset bits  (A[1:0]) = 00 → aligned on 4 bytes boundary
    Bank bits    selects the bank, e.g for 4 banks (A[3:2]) = 00 → Bank 0, 01 → Bank 1, 10 → Bank 2, 11 → Bank 3
    Row bits     remaining bits → Row address within the bank
 *   
 * Top level for the log interconnect
 */

//import isolde_soc_package::*;

module isolde_log_interconnect
  import tcdm_interconnect_pkg::topo_e;
#(
    parameter int unsigned N_SLAVES  = 1,
    parameter int unsigned N_MASTERS = 9,
    parameter int unsigned TCDM_AW   = isolde_tcdm_pkg::TCDM_AW  // Address Width TCDM Memory
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  isolde_tcdm_pkg::req_t cores_req_i[ N_SLAVES-1:0],
    output isolde_tcdm_pkg::rsp_t cores_rsp_o[ N_SLAVES-1:0],
    output isolde_tcdm_pkg::req_t mems_req_o [N_MASTERS-1:0],
    input  isolde_tcdm_pkg::rsp_t mems_rsp_i [N_MASTERS-1:0]

);
  //localparam int unsigned NumOutLog2 = $clog2(N_MASTERS);
  localparam int unsigned AWC = isolde_tcdm_pkg::CORE_AW;  // Address Width Cor
  localparam int unsigned DW = isolde_tcdm_pkg::CORE_DW;  // Data Width
  localparam int unsigned ByteOffWidth = $clog2(DW - 1) - 3;  // Byte Offset Width
  localparam int unsigned UW = 0;  // User Width, not used in this interconnect
  localparam int unsigned BW = 8;  // Byte Width
  //localparam int unsigned IW  = 0;  // ID Width, not used in this interconnect

  // master side
  logic [ N_SLAVES-1:0]              cores_req;
  logic [ N_SLAVES-1:0][    AWC-1:0] cores_add;
  logic [ N_SLAVES-1:0]              cores_wen;
  logic [ N_SLAVES-1:0][  UW+DW-1:0] cores_wdata;
  logic [ N_SLAVES-1:0][  DW/BW-1:0] cores_be;
  logic [ N_SLAVES-1:0]              cores_gnt;
  logic [ N_SLAVES-1:0]              cores_r_valid;
  logic [ N_SLAVES-1:0][  UW+DW-1:0] cores_r_rdata;
  // slave side
  logic [N_MASTERS-1:0]              mems_req;
  logic [N_MASTERS-1:0][TCDM_AW-1:0] mems_add;
  logic [N_MASTERS-1:0]              mems_wen;
  logic [N_MASTERS-1:0][  UW+DW-1:0] mems_wdata;
  logic [N_MASTERS-1:0][  DW/BW-1:0] mems_be;
  //  logic [N_MASTERS-1:0][   IW-1:0] mems_ID;
  logic [N_MASTERS-1:0]              mems_gnt;
  logic [N_MASTERS-1:0][  UW+DW-1:0] mems_r_rdata;
  logic [N_MASTERS-1:0]              mems_r_valid;
  //logic [N_MASTERS-1:0][   IW-1:0] mems_r_ID;

  // interface unrolling
  generate
    for (genvar i = 0; i < N_SLAVES; i++) begin : cores_unrolling
      wire isolde_tcdm_pkg::req_t _s_core_req;
      assign _s_core_req = cores_req_i[i];
      wire isolde_tcdm_pkg::rsp_t _s_core_rsp;
      assign cores_rsp_o[i]    = _s_core_rsp;
      //request
      assign cores_req[i]      = _s_core_req.req;
      assign cores_wen[i]      = ~_s_core_req.we;
      assign cores_be[i]       = _s_core_req.be;
      assign cores_add[i]      = _s_core_req.addr;
      assign cores_wdata[i]    = _s_core_req.data;
      //response
      assign _s_core_rsp.gnt   = cores_gnt[i];
      assign _s_core_rsp.valid = cores_r_valid[i];
      assign _s_core_rsp.err   = '0;
      assign _s_core_rsp.data  = cores_r_rdata[i];
    end  // cores_unrolling
  endgenerate

  generate
    for (genvar jj = 0; jj < N_MASTERS; jj++) begin
      wire isolde_tcdm_pkg::req_t _s_mem_req;
      assign mems_req_o[jj] = _s_mem_req;
      wire isolde_tcdm_pkg::rsp_t _s_mem_rsp;
      assign _s_mem_rsp                     = mems_rsp_i[jj];
      //request
      assign _s_mem_req.req                 = mems_req[jj];
      assign _s_mem_req.we                  = ~mems_wen[jj];
      assign _s_mem_req.be                  = mems_be[jj];
      // add_i[j][ByteOffWidth+NumOutLog2+AddrMemWidth-1:ByteOffWidth+NumOutLog2], wdata_i[j]};
      assign _s_mem_req.addr[1:0]           = '0;
      assign _s_mem_req.addr[TCDM_AW-1:2]   = mems_add[jj];
      assign _s_mem_req.addr[AWC-1:TCDM_AW] = '0;  // zero padding for address width
      assign _s_mem_req.data                = mems_wdata[jj];
      //response
      assign mems_gnt[jj]                   = _s_mem_rsp.gnt;
      assign mems_r_valid[jj]               = _s_mem_rsp.valid;
      assign mems_r_rdata[jj]               = _s_mem_rsp.data;


    end  // mems_unrolling
  endgenerate

  // uses XBAR_TCDM from cluster_interconnect
  tcdm_interconnect #(
      .NumIn       (N_SLAVES),
      .NumOut      (N_MASTERS),
      .AddrWidth   (AWC),
      .DataWidth   (DW + UW),
      .ByteOffWidth(ByteOffWidth),               // determine byte offset from real data width
      .AddrMemWidth(TCDM_AW),
      .WriteRespOn (1),
      .RespLat     (1),
      .BeWidth     (DW / BW),
      .Topology    (tcdm_interconnect_pkg::LIC)
  ) i_tcdm_interconnect (
      .clk_i,
      .rst_ni,

      .req_i  (cores_req),
      .add_i  (cores_add),
      .wen_i  (cores_wen),
      .wdata_i(cores_wdata),
      .be_i   (cores_be),
      .gnt_o  (cores_gnt),
      .vld_o  (cores_r_valid),
      .rdata_o(cores_r_rdata),

      .req_o  (mems_req),
      .gnt_i  (mems_gnt),
      .add_o  (mems_add),
      .wen_o  (mems_wen),
      .wdata_o(mems_wdata),
      .be_o   (mems_be),
      .rdata_i(mems_r_rdata)
  );

endmodule  // isolde_log_interconnect
