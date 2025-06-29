// Copyleft 2024 ISOLDE
// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Yvan Tortorella <yvan.tortorella@unibo.it>
//

`include "periph_bus_defines.sv"

timeunit 1ps; timeprecision 1ps;

module tb_lca_system (
    input logic clk_i,
    input logic rst_ni,
    input logic fetch_enable_i

);
  import redmule_pkg::*;
  //ibex parameters
  parameter bit SecureIbex = 1'b0;
  parameter bit ICacheScramble = 1'b0;
  parameter bit PMPEnable = 1'b0;
  parameter int unsigned PMPGranularity = 0;
  parameter int unsigned PMPNumRegions = 4;
  parameter int unsigned MHPMCounterNum = 0;
  parameter int unsigned MHPMCounterWidth = 40;
  parameter bit RV32E = 1'b0;
  parameter ibex_pkg::rv32m_e RV32M = `RV32M;
  parameter ibex_pkg::rv32b_e RV32B = `RV32B;
  parameter ibex_pkg::regfile_e RegFile = `RegFile;
  parameter bit BranchTargetALU = 1'b0;
  parameter bit WritebackStage = 1'b0;
  parameter bit ICache = 1'b0;
  parameter bit DbgTriggerEn = 1'b1;
  parameter bit ICacheECC = 1'b0;
  parameter bit BranchPredictor = 1'b0;
  parameter int unsigned IMEM_LATENCY = 0;
  // parameters
  localparam int unsigned NC = 1;
  localparam int unsigned ID = 10;
  localparam int unsigned DW = redmule_pkg::DATA_W;
  localparam int unsigned MP = DW / 32;
  localparam int unsigned MEMORY_SIZE = 32'h30000;
  localparam int unsigned STACK_MEMORY_SIZE = 32'h30000;
  localparam int unsigned PULP_XPULP = 1;
  localparam int unsigned FPU = 0;
  localparam int unsigned PULP_ZFINX = 0;
  localparam logic [31:0] BASE_ADDR = 32'h1c000000;
  localparam logic [31:0] HWPE_ADDR_BASE_BIT = 20;

  int fh, fh_csv;  //filehandles
  //
  /* see bsp/link.ld
MEMORY
{
    instrram    : ORIGIN = 0x00100000, LENGTH = 0x8000
    dataram     : ORIGIN = 0x00110000, LENGTH = 0x30000
    stack       : ORIGIN = 0x00140000, LENGTH = 0x30000
}
*/
  localparam logic [31:0] IMEM_ADDR = 32'h00100000;
  localparam int unsigned IMEM_SIZE = 32'h08000;
  localparam logic [31:0] DMEM_ADDR = 32'h00110000;
  localparam int unsigned DMEM_SIZE = 32'h30000;
  localparam logic [31:0] SMEM_ADDR = 32'h00140000;
  localparam int unsigned SMEM_SIZE = 32'h30000;
  localparam int unsigned GMEM_SIZE = SMEM_ADDR + SMEM_SIZE - IMEM_ADDR;
  //  see reset vector in bsp/crt0.S
  localparam logic [31:0] BOOT_ADDR = 32'h00100080;
  localparam logic [31:0] PERI_ADDR = 32'h00001000;
  //see bsp/simple_system_regs.h
  localparam logic [31:0] MMIO_ADDR = 32'h80000000;
  localparam logic [31:0] MMADDR_EXIT = MMIO_ADDR + 32'h0;
  localparam logic [31:0] MMADDR_PRINT = MMIO_ADDR + 32'h4;
  localparam logic [31:0] MMADDR_TTY = MMIO_ADDR + 32'h8;
  localparam logic [31:0] MMADDR_PERF = MMIO_ADDR + 32'hC;


  // global signals
  string stim_instr, stim_data;
  logic        test_mode;
  logic [31:0] cycle_counter;
  logic        mmio_rvalid;
  logic        mmio_req;
  logic        mmio_gnt;
  logic [31:0] mmio_rdata;
  //
  logic        perfcnt_rvalid;
  logic        perfcnt_req;
  logic        perfcnt_gnt;
  logic [31:0] perfcnt_rdata;
  //
  logic        redmule_busy;

  
    // jtag openocd bridge signals
    logic                        sim_jtag_tck;
    logic                        sim_jtag_tms;
    logic                        sim_jtag_tdi;
    logic                        sim_jtag_trstn;
    logic                        sim_jtag_tdo;
    logic [31:0]                 sim_jtag_exit;
    logic                        sim_jtag_enable;

    // signals for debug unit
    logic                        debug_req_ready;
    dm::dmi_resp_t               debug_resp;
    logic                        jtag_req_valid;
    dm::dmi_req_t                jtag_dmi_req;
    logic                        jtag_resp_ready;
    logic                        jtag_resp_valid;
    logic [NrHarts-1:0]          dm_debug_req;
    logic                        ndmreset, ndmreset_n;

    // debug unit slave interface
    logic                        dm_grant;
    logic                        dm_rvalid;
    logic                        dm_req;
    logic                        dm_we;
    logic [31:0]                 dm_addr;
    logic [31:0]                 dm_wdata;
    logic [31:0]                 dm_rdata;
    logic [3:0]                  dm_be;

    // debug unit master interface (system bus access)
    logic                        sb_req;
    logic [31:0]                 sb_addr;
    logic                        sb_we;
    logic [31:0]                 sb_wdata;
    logic [3:0]                  sb_be;
    logic                        sb_gnt;
    logic                        sb_rvalid;
    logic [31:0]                 sb_rdata;

    // irq signals (not used)
    logic                        irq;
    logic [0:4]                  irq_id_in;
    logic                        irq_ack;
    logic [0:4]                  irq_id_out;

   localparam  bit          JTAG_BOOT = 1;
     localparam int unsigned  OPENOCD_PORT = 9999;
       localparam CLUSTER_ID         = 6'd0;
    localparam CORE_ID            = 4'd0;

    localparam CORE_MHARTID       = {21'b0, CLUSTER_ID, 1'b0, CORE_ID};
    localparam NrHarts                               = 1;
    localparam logic [NrHarts-1:0] SELECTABLE_HARTS  = 1 << CORE_MHARTID;
    localparam HARTINFO           = {8'h0, 4'h2, 3'b0, 1'b1, dm::DataCount, dm::DataAddr};
    // make jtag bridge work
    assign sim_jtag_enable = JTAG_BOOT;

  //hwpe_stream_intf_tcdm instr[0:0] (.clk(clk_i));
  hwpe_stream_intf_tcdm stack[0:0] (.clk(clk_i));
  hwpe_stream_intf_tcdm tcdm[MP+1:0] (.clk(clk_i));

  logic [NC-1:0][ 1:0] evt;
  logic [MP-1:0]       tcdm_gnt;
  logic [MP-1:0][31:0] tcdm_r_data;
  logic [MP-1:0]       tcdm_r_valid;

  logic                core_sleep;

  // typedef struct packed {
  //   logic        req;
  //   logic [31:0] addr;
  // } core_inst_req_t;

  // typedef struct packed {
  //   logic        gnt;
  //   logic        valid;
  //   logic [31:0] data;
  // } core_inst_rsp_t;

  typedef struct {
    logic req;
    logic we;
    logic [3:0] be;
    logic [31:0] addr;
    logic [31:0] data;
  } core_data_req_t;

  typedef struct {
    logic gnt;
    logic valid;
    logic [31:0] data;
  } core_data_rsp_t;

  hci_core_intf #(.DW(DW)) redmule_tcdm (.clk(clk_i));
  hwpe_ctrl_intf_periph #(.ID_WIDTH(ID)) periph (.clk(clk_i));

  //core_inst_req_t core_inst_req;
  // core_inst_rsp_t core_inst_rsp;
  isolde_tcdm_if tcdm_core_inst ();
  isolde_tcdm_if tcdm_core_inst_shim ();

  core_data_req_t core_data_req;
  core_data_rsp_t core_data_rsp;



  
    // debug subsystem
    dmi_jtag #(
        .IdcodeValue          ( 32'h249511C3    )
    ) i_dmi_jtag (
        .clk_i                ( clk_i           ),
        .rst_ni               ( rst_ni          ),
        .testmode_i           ( 1'b0            ),
        .dmi_req_o            ( jtag_dmi_req    ),
        .dmi_req_valid_o      ( jtag_req_valid  ),
        .dmi_req_ready_i      ( debug_req_ready ),
        .dmi_resp_i           ( debug_resp      ),
        .dmi_resp_ready_o     ( jtag_resp_ready ),
        .dmi_resp_valid_i     ( jtag_resp_valid ),
        .dmi_rst_no           (                 ), // not connected
        .tck_i                ( sim_jtag_tck    ),
        .tms_i                ( sim_jtag_tms    ),
        .trst_ni              ( sim_jtag_trstn  ),
        .td_i                 ( sim_jtag_tdi    ),
        .td_o                 ( sim_jtag_tdo    ),
        .tdo_oe_o             (                 )
    );

    dm_top #(
       .NrHarts           ( NrHarts           ),
       .BusWidth          ( 32                ),
       .SelectableHarts   ( SELECTABLE_HARTS  )
    ) i_dm_top (

       .clk_i             ( clk_i             ),
       .rst_ni            ( rst_ni            ),
       .testmode_i        ( 1'b0              ),
       .ndmreset_o        ( ndmreset          ),
       .dmactive_o        (                   ), // active debug session TODO
       .debug_req_o       ( dm_debug_req      ),
       .unavailable_i     ( ~SELECTABLE_HARTS ),
       .hartinfo_i        ( HARTINFO          ),

       .slave_req_i       ( dm_req            ),
       .slave_we_i        ( dm_we             ),
       .slave_addr_i      ( dm_addr           ),
       .slave_be_i        ( dm_be             ),
       .slave_wdata_i     ( dm_wdata          ),
       .slave_rdata_o     ( dm_rdata          ),

       .master_req_o      ( sb_req            ),
       .master_add_o      ( sb_addr           ),
       .master_we_o       ( sb_we             ),
       .master_wdata_o    ( sb_wdata          ),
       .master_be_o       ( sb_be             ),
       .master_gnt_i      ( sb_gnt            ),
       .master_r_valid_i  ( sb_rvalid         ),
       .master_r_rdata_i  ( sb_rdata          ),

       .dmi_rst_ni        ( rst_ni            ),
       .dmi_req_valid_i   ( jtag_req_valid    ),
       .dmi_req_ready_o   ( debug_req_ready   ),
       .dmi_req_i         ( jtag_dmi_req      ),
       .dmi_resp_valid_o  ( jtag_resp_valid   ),
       .dmi_resp_ready_i  ( jtag_resp_ready   ),
       .dmi_resp_o        ( debug_resp        )
    );

//  // jtag calls from dpi
//     SimJTAG #(
//         .TICK_DELAY (1),
//         .PORT(OPENOCD_PORT)
//     ) i_sim_jtag (
//         .clock                ( clk_i                ),
//         .reset                ( ~rst_ni              ),
//         .enable               ( sim_jtag_enable      ),
//         .init_done            ( rst_ni               ),
//         .jtag_TCK             ( sim_jtag_tck         ),
//         .jtag_TMS             ( sim_jtag_tms         ),
//         .jtag_TDI             ( sim_jtag_tdi         ),
//         .jtag_TRSTn           ( sim_jtag_trstn       ),
//         .jtag_TDO_data        ( sim_jtag_tdo         ),
//         .jtag_TDO_driven      ( 1'b1                 ),
//         .exit                 ( sim_jtag_exit        )
//     );

//     always_comb begin : jtag_exit_handler
//         if (sim_jtag_exit)
//             $finish(2); // print stats too
//     end

  // --------
  // AXI Typedefs
  // --------
  localparam int unsigned PhysicalAddrWidth = 32;
  localparam int unsigned DataWidth = 32;
  localparam int unsigned IdWidth = 1;
  localparam int unsigned UserWidth = 1;
  typedef logic [PhysicalAddrWidth-1:0] addr_t;
  typedef logic [IdWidth-1:0] id_mst_t;
  typedef logic [DataWidth-1:0] data_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [UserWidth-1:0] user_t;

  `AXI_TYPEDEF_ALL(axi_imem, addr_t, id_mst_t, data_t, strb_t, user_t)
  axi_imem_req_t  axi_imem_req;
  axi_imem_resp_t axi_imem_resp;

  // performance counters FSM states
  typedef enum logic [2:0] {
    IDLE,
    LATCH,
    WAIT,
    DIFF,
    PRINT
  } perfcnt_state_t;

  typedef struct packed {
    int cnt_wr;
    int cnt_rd;
  } mem_io_t;

  typedef struct packed {
    logic [31:0] id;
    logic [31:0] cycle_counter;
    mem_io_t imem;
    mem_io_t dmem;
    mem_io_t stack_mem;
  } perfcnt_t;


  perfcnt_state_t perfcnt_state, perfcnt_next;
  perfcnt_t perfcnt_d, perfcnt_q;

  always_ff @(posedge clk_i) begin
    if (~rst_ni) begin
      perfcnt_d <= '0;
      perfcnt_q <= '0;
      perfcnt_state = IDLE;
    end else begin
      perfcnt_state <= perfcnt_next;
      case (perfcnt_next)
        LATCH: begin
          perfcnt_d.id <= core_data_req.data;
          perfcnt_d.cycle_counter <= cycle_counter;
          perfcnt_d.dmem.cnt_wr <= tb_lca_system.i_dummy_dmemory.cnt_wr;
          perfcnt_d.dmem.cnt_rd <= tb_lca_system.i_dummy_dmemory.cnt_rd;
          //perfcnt_d.imem.cnt_rd <= tb_lca_system.i_dummy_imemory.cnt_rd;
          perfcnt_d.stack_mem.cnt_wr <= tb_lca_system.i_dummy_stack_memory.cnt_wr;
          perfcnt_d.stack_mem.cnt_rd <= tb_lca_system.i_dummy_stack_memory.cnt_rd;
          //$display("LATCH @%t id=%d,cycle_counter=%d\n",$time, core_data_req.data,cycle_counter);
        end
        DIFF: begin
          perfcnt_q.id <= perfcnt_d.id;
          perfcnt_q.cycle_counter <= (cycle_counter - perfcnt_d.cycle_counter);
          perfcnt_q.dmem.cnt_wr <= (tb_lca_system.i_dummy_dmemory.cnt_wr - perfcnt_d.dmem.cnt_wr);
          perfcnt_q.dmem.cnt_rd <= (tb_lca_system.i_dummy_dmemory.cnt_rd - perfcnt_d.dmem.cnt_rd);
          //
          //perfcnt_q.imem.cnt_rd <= (tb_lca_system.i_dummy_imemory.cnt_rd - perfcnt_d.imem.cnt_rd);
          //
          perfcnt_q.stack_mem.cnt_wr <= (tb_lca_system.i_dummy_stack_memory.cnt_wr-perfcnt_d.stack_mem.cnt_wr);
          perfcnt_q.stack_mem.cnt_rd <= (tb_lca_system.i_dummy_stack_memory.cnt_rd-perfcnt_d.stack_mem.cnt_rd);

          //$display("DIFF @%t id=%d,cycle_counter=%h\n",$time,  perfcnt_d.id, cycle_counter);
        end
        PRINT: begin
          //$display("PRINT @%t id=%d,cycles =%d\n", $time, perfcnt_q.id, perfcnt_q.cycle_counter);
          $fwrite(fh_csv, "%d,%d,", perfcnt_q.id, perfcnt_q.cycle_counter);
          $fwrite(fh_csv, "%d,", perfcnt_q.imem.cnt_rd);
          $fwrite(fh_csv, "%d,", perfcnt_q.dmem.cnt_wr);
          $fwrite(fh_csv, "%d,", perfcnt_q.dmem.cnt_rd);
          $fwrite(fh_csv, "%d,", perfcnt_q.stack_mem.cnt_wr);
          $fwrite(fh_csv, "%d,", perfcnt_q.stack_mem.cnt_rd);
          $fwrite(fh_csv, "%d,LCA\n", IMEM_LATENCY);
        end
      endcase
    end

  end


  always_comb begin
    perfcnt_req = rst_ni && core_data_req.req && (core_data_req.addr >= MMADDR_PERF);
    perfcnt_gnt = perfcnt_req;
    if (perfcnt_req && core_data_req.we && (core_data_req.addr == MMADDR_PERF)) begin
      case (perfcnt_state)
        IDLE: begin
          perfcnt_next = LATCH;
        end
        WAIT: begin
          perfcnt_next = DIFF;
        end
      endcase
    end else begin
      case (perfcnt_state)
        LATCH: begin
          perfcnt_next = WAIT;
        end
        DIFF: begin
          perfcnt_next = PRINT;
        end
        PRINT: begin
          perfcnt_next = IDLE;
        end
      endcase
    end
  end

  /**
read performance counters implementation
**/

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) perfcnt_rvalid <= '0;
    else begin
      if (perfcnt_req) begin
        perfcnt_rvalid <= 1;
        if (~core_data_req.we) begin
          case (core_data_req.addr)
            MMADDR_PERF: perfcnt_rdata <= perfcnt_q.id;
            MMADDR_PERF + 32'h4: perfcnt_rdata <= perfcnt_q.cycle_counter;
            MMADDR_PERF + 32'h8: perfcnt_rdata <= perfcnt_q.imem.cnt_wr;
            MMADDR_PERF + 32'hC: perfcnt_rdata <= perfcnt_q.imem.cnt_rd;
            MMADDR_PERF + 32'h10: perfcnt_rdata <= perfcnt_q.dmem.cnt_wr;
            MMADDR_PERF + 32'h14: perfcnt_rdata <= perfcnt_q.dmem.cnt_rd;
            MMADDR_PERF + 32'h18: perfcnt_rdata <= perfcnt_q.stack_mem.cnt_wr;
            MMADDR_PERF + 32'h1C: perfcnt_rdata <= perfcnt_q.stack_mem.cnt_rd;
            default: perfcnt_rdata <= '0;
          endcase
        end
      end else perfcnt_rvalid = '0;
    end
  end




  always_comb begin : bind_periph
    periph.req    = core_data_req.req &
                         (core_data_req.addr >= PERI_ADDR) &
                         (core_data_req.addr < IMEM_ADDR) ;
    periph.add = core_data_req.addr;
    periph.wen = ~core_data_req.we;
    periph.be = core_data_req.be;
    periph.data = core_data_req.data;
    periph.id = '0;
    //periph_r_valid = '0;
  end

  // always_comb begin : bind_instrs
  //   tcdm[MP+1].req = tcdm_core_inst_shim.req.req;
  //   tcdm[MP+1].add = tcdm_core_inst_shim.req.addr;
  //   tcdm[MP+1].wen = 1'b1;
  //   tcdm[MP+1].be = '0;
  //   tcdm[MP+1].data = '0;
  //   tcdm_core_inst_shim.rsp.gnt = tcdm[MP+1].gnt;
  //   tcdm_core_inst_shim.rsp.valid = tcdm[MP+1].r_valid;
  //   tcdm_core_inst_shim.rsp.data = tcdm[MP+1].r_data;
  // end


  always_comb begin : bind_stack
    stack[0].req  = core_data_req.req & (core_data_req.addr >= SMEM_ADDR) &
                                        (core_data_req.addr < SMEM_ADDR+SMEM_SIZE) ;
    stack[0].add = core_data_req.addr;
    stack[0].wen = ~core_data_req.we;
    stack[0].be = core_data_req.be;
    stack[0].data = core_data_req.data;
  end




  for (genvar ii = 0; ii < MP; ii++) begin : tcdm_binding
    assign tcdm[ii].req     = redmule_tcdm.req;
    assign tcdm[ii].add     = redmule_tcdm.add + ii * 4;
    assign tcdm[ii].wen     = redmule_tcdm.wen;
    assign tcdm[ii].be      = redmule_tcdm.be[(ii+1)*4-1:ii*4];
    assign tcdm[ii].data    = redmule_tcdm.data[(ii+1)*32-1:ii*32];
    assign tcdm_gnt[ii]     = tcdm[ii].gnt;
    assign tcdm_r_valid[ii] = tcdm[ii].r_valid;
    assign tcdm_r_data[ii]  = tcdm[ii].r_data;
  end
  assign redmule_tcdm.gnt = &tcdm_gnt;
  assign redmule_tcdm.r_data = {tcdm_r_data};
  assign redmule_tcdm.r_valid = &tcdm_r_valid;
  assign redmule_tcdm.r_opc = '0;
  assign redmule_tcdm.r_user = '0;

  assign tcdm[MP].req  = core_data_req.req &
                         (core_data_req.addr >= DMEM_ADDR) &
                         (core_data_req.addr <  DMEM_ADDR + DMEM_SIZE) ;
  assign tcdm[MP].add = core_data_req.addr;
  assign tcdm[MP].wen = ~core_data_req.we;
  assign tcdm[MP].be = core_data_req.be;
  assign tcdm[MP].data = core_data_req.data;

  assign core_data_rsp.gnt =  periph.req ?
                       periph.gnt : stack[0].req ?
                                    stack[0].gnt : tcdm[MP].req ?
                                                   tcdm[MP].gnt : mmio_req ?
                                                                  mmio_gnt : perfcnt_req ?
                                                                             perfcnt_gnt : '1;

  assign core_data_rsp.data = periph.r_valid   ? periph.r_data    :
                                        stack[0].r_valid ? stack[0].r_data  :
                                                           tcdm[MP].r_valid ? tcdm[MP].r_data : 
                                                                              mmio_rvalid ? mmio_rdata:
                                                                                            perfcnt_rvalid ? perfcnt_rdata :'0;
  assign core_data_rsp.valid = periph.r_valid | stack[0].r_valid | tcdm[MP].r_valid | mmio_rvalid | perfcnt_rvalid;









  tb_tcdm_verilator #(
      .MP         (MP + 1),
      .MEMORY_SIZE(GMEM_SIZE),
      .BASE_ADDR  (IMEM_ADDR)
  ) i_dummy_dmemory (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .enable_i(1'b1),
      .tcdm    (tcdm[MP:0])
  );

  isolde_addr_shim #(
      .START_ADDR(IMEM_ADDR),  // Set start address
      .END_ADDR(IMEM_ADDR + GMEM_SIZE)  // Set end address
  ) dut (
      .tcdm_slave_i (tcdm_core_inst),
      .tcdm_master_o(tcdm_core_inst_shim)
  );
  
  isolde_tcdm_to_axi #(
      .axi_req_t(axi_imem_req_t),
      .axi_rsp_t(axi_imem_resp_t)
  ) i_imem_to_axi (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .s_tcdm(tcdm_core_inst_shim),
      .slv_aw_cache_i(),
      .slv_ar_cache_i(),
      .axi_req_o(axi_imem_req),
      .axi_rsp_i(axi_imem_resp)

  );

  isolde_axi_sim_mem #(
      .MEMORY_SIZE(GMEM_SIZE),
      .axi_req_t(axi_imem_req_t),
      .axi_rsp_t(axi_imem_resp_t)
  ) i_dummy_imemory (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .axi_req_i(axi_imem_req),
      .axi_rsp_o(axi_imem_resp)
  );

  // tb_tcdm_verilator #(
  //     .MP          (1),
  //     .MEMORY_SIZE (GMEM_SIZE),
  //     .BASE_ADDR   (0),
  //     .DELAY_CYCLES(IMEM_LATENCY)
  // ) i_dummy_imemory (
  //     .clk_i   (clk_i),
  //     .rst_ni  (rst_ni),
  //     .enable_i(1'b1),
  //     .tcdm    (tcdm[MP+1:MP+1])
  // );

  tb_tcdm_verilator #(
      .MP         (1),
      .MEMORY_SIZE(SMEM_SIZE),
      .BASE_ADDR  (SMEM_ADDR)
  ) i_dummy_stack_memory (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .enable_i(1'b1),
      .tcdm    (stack)
  );

  isolde_cv_x_if #(
      .X_NUM_RS   (isolde_cv_x_if_pkg::X_NUM_RS),
      .X_ID_WIDTH (isolde_cv_x_if_pkg::X_ID_WIDTH),
      .X_MEM_WIDTH(isolde_cv_x_if_pkg::X_MEM_WIDTH),
      .X_RFR_WIDTH(isolde_cv_x_if_pkg::X_RFR_WIDTH),
      .X_RFW_WIDTH(isolde_cv_x_if_pkg::X_RFW_WIDTH),
      .X_MISA     (isolde_cv_x_if_pkg::X_MISA),
      .X_ECS_XS   (isolde_cv_x_if_pkg::X_ECS_XS)
  ) core_xif ();

  xif_monitor_cpu_issue xif_monitor_cpu_issue_i (
      clk_i,
      core_xif
  );

  ibex_top_tracing #(
      .SecureIbex      (SecureIbex),
      .ICacheScramble  (ICacheScramble),
      .PMPEnable       (PMPEnable),
      .PMPGranularity  (PMPGranularity),
      .PMPNumRegions   (PMPNumRegions),
      .MHPMCounterNum  (MHPMCounterNum),
      .MHPMCounterWidth(MHPMCounterWidth),
      .RV32E           (RV32E),
      .RV32M           (RV32M),
      .RV32B           (RV32B),
      .RegFile         (RegFile),
      .BranchTargetALU (BranchTargetALU),
      .ICache          (ICache),
      .ICacheECC       (ICacheECC),
      .WritebackStage  (WritebackStage),
      .BranchPredictor (BranchPredictor),
      .DbgTriggerEn    (DbgTriggerEn),
      .DmHaltAddr      (`DEBUG_START_ADDR + dm::HaltAddress[31:0] ),
      .DmExceptionAddr (`DEBUG_START_ADDR + dm::ExceptionAddress[31:0])
  ) u_top (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .test_en_i  (1'b0),
      .scan_rst_ni(1'b1),
      .ram_cfg_i  (prim_ram_1p_pkg::RAM_1P_CFG_DEFAULT),

      .hart_id_i        (32'b0),
      // First instruction executed is at 0x0 + 0x80
      .boot_addr_i      (BOOT_ADDR),
      // Instruction memory interface
      .instr_req_o      (tcdm_core_inst.req.req),
      .instr_gnt_i      (tcdm_core_inst.rsp.gnt),
      .instr_rvalid_i   (tcdm_core_inst.rsp.valid),
      .instr_addr_o     (tcdm_core_inst.req.addr),
      .instr_rdata_i    (tcdm_core_inst.rsp.data),
      //.instr_rdata_intg_i     (instr_rdata_intg),
      //.instr_err_i            (instr_err),
      //     // Data memory interface
      .data_req_o       (core_data_req.req),
      .data_gnt_i       (core_data_rsp.gnt),
      .data_rvalid_i    (core_data_rsp.valid),
      .data_addr_o      (core_data_req.addr),
      .data_be_o        (core_data_req.be),
      .data_we_o        (core_data_req.we),
      .data_wdata_o     (core_data_req.data),
      .data_wdata_intg_o(),
      .data_rdata_i     (core_data_rsp.data),
      .data_rdata_intg_i(),
      .data_err_i       (),

      .irq_software_i(evt[0][0]),
      .irq_timer_i   (1'b0),
      .irq_external_i(1'b0),
      .irq_fast_i    (1'b0),
      .irq_nm_i      (1'b0),

      .scramble_key_valid_i('0),
      .scramble_key_i      ('0),
      .scramble_nonce_i    ('0),
      .scramble_req_o      (),

      .debug_req_i        (dm_debug_req[0]),
      .crash_dump_o       (),
      .double_fault_seen_o(),

      .fetch_enable_i        (fetch_enable_i),
      .alert_minor_o         (),
      .alert_major_internal_o(),
      .alert_major_bus_o     (),
      .core_sleep_o          (core_sleep),
      // eXtension interface
      .xif_compressed_if     (core_xif.cpu_compressed),
      .xif_issue_if          (core_xif.cpu_issue),
      .xif_commit_if         (core_xif.cpu_commit),
      .xif_mem_if            (core_xif.cpu_mem),
      .xif_mem_result_if     (core_xif.cpu_mem_result),
      .xif_result_if         (core_xif.cpu_result)
  );
  redmule_isolde #(
      .ID_WIDTH (ID),
      .N_CORES  (NC),
      .DW       (DW),  // TCDM port dimension (in bits
      .AddrWidth(32)
  ) i_dut (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .test_mode_i   (test_mode),
      .fetch_enable_i(fetch_enable_i),
      .evt_o         (evt),
      .tcdm          (redmule_tcdm),
      .periph        (periph)
  );




  // Declare the task with an input parameter for errors
  task endSimulation(input int errors);
    if (errors != 0) begin
      $display("[TB LCA] @ t=%0t - Fail!", $time);
      //      $error("[TB LCA] @ t=%0t - errors=%08x", $time, errors);
      $display("[TB LCA] @ t=%0t - errors=%08x", $time, errors);
    end else begin
      $display("[TB LCA] @ t=%0t - Success!", $time);
      $display("[TB LCA] @ t=%0t - errors=%08x", $time, errors);
    end
    // $fwrite(fh, "[TB LCA] @ t=%0t - writes[imemory] =%d\n", $time,
    //        tb_lca_system.i_dummy_imemory.cnt_wr);
    // $fwrite(fh, "[TB LCA] @ t=%0t - reads [imemory] =%d\n", $time,
    //         tb_lca_system.i_dummy_imemory.cnt_rd);
    //
    $fwrite(fh, "[TB LCA] @ t=%0t - writes[dmemory] =%d\n", $time,
            tb_lca_system.i_dummy_dmemory.cnt_wr);
    $fwrite(fh, "[TB LCA] @ t=%0t - reads [dmemory] =%d\n", $time,
            tb_lca_system.i_dummy_dmemory.cnt_rd);
    //
    $fwrite(fh, "[TB LCA] @ t=%0t - writes[stack] =%d\n", $time,
            tb_lca_system.i_dummy_stack_memory.cnt_wr);
    $fwrite(fh, "[TB LCA] @ t=%0t - reads [stack] =%d\n", $time,
            tb_lca_system.i_dummy_stack_memory.cnt_rd);
    $finish;
  endtask

  /*
** The semantics of the r_valid signal are not well defined with respect to the usual TCDM protocol. In PULP clusters, r_valid will be asserted also after write transactions, not only in reads. 
** https://hwpe-doc.readthedocs.io/en/latest/protocols.html#hwpe-mem
** see also https://ibex-core.readthedocs.io/en/latest/03_reference/load_store_unit.html
**/

  always_comb begin
    mmio_req =  core_data_req.req && (core_data_req.addr >= MMIO_ADDR) && (core_data_req.addr < MMADDR_PERF) ;
    mmio_gnt = mmio_req;
  end



  always_ff @(posedge clk_i) begin
    if (~rst_ni) begin
      cycle_counter <= '0;
      mmio_rvalid   <= 0;
    end else cycle_counter <= cycle_counter + 1;

    if (mmio_gnt) begin
      case (core_data_req.addr)
        MMADDR_EXIT: begin
          if (core_data_req.we) endSimulation(core_data_req.data);
          else begin
            mmio_rdata  <= cycle_counter + 1;
            mmio_rvalid <= 1;
          end

        end
        MMADDR_PRINT:
        if (core_data_req.we) begin
          $write("%c", core_data_req.data);
          mmio_rvalid <= 1;
        end
        MMADDR_TTY:
        if (core_data_req.we) begin
          $display("TTY @t=%0t: %h", $time, core_data_req.data);
          //$write("%c", core_data_req.data);
          mmio_rvalid <= 1;
        end
        default: begin
          mmio_rdata  <= '0;
          mmio_rvalid <= 0;
        end
      endcase
    end else mmio_rvalid <= 0;

  end


  initial begin
    integer id;
    int cnt_rd, cnt_wr;
    fh = $fopen("rtl_debug_trace.log", "w");
    fh_csv = $fopen("perfcnt.csv", "w");
    $fwrite(
        fh_csv,
        "id,cycles,reads[imemory],writes[dmemory],reads[dmemory],writes[stack],reads[stack],latency,arch\n");
    // Load instruction and data memory
    if (!$value$plusargs("STIM_INSTR=%s", stim_instr)) begin
      $display("No STIM_INSTR specified");
      $finish;
    end else begin
      $display("[TESTBENCH] @ t=%0t: loading %0s into imemory", $time, stim_instr);
      $readmemh(stim_instr, tb_lca_system.i_dummy_imemory.i_mem.memory);
    end

    if (!$value$plusargs("STIM_DATA=%s", stim_data)) begin
      $display("No STIM_DATA specified");
      $finish;
    end else begin
      $display("[TESTBENCH] @ t=%0t: loading %0s into dmemory", $time, stim_data);
      $readmemh(stim_data, tb_lca_system.i_dummy_dmemory.memory);
    end
   
    test_mode = 1'b0;

  end

  // close output file for writing
  final begin

    $fclose(fh);
    $fclose(fh_csv);

  end
endmodule  // tb_lca_system
