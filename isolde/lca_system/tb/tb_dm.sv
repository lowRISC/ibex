// Copyleft 2024 ISOLDE
// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Yvan Tortorella <yvan.tortorella@unibo.it>
//

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
  parameter bit DbgTriggerEn = 1'b0;
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


  localparam int unsigned RuleAddrWidth = 32;
  typedef logic [RuleAddrWidth-1:0] rule_addr_t;

  typedef enum logic [3:0] {
    INVALID,
    PERIPH_IDX,
    DATA_IDX,
    STACK_IDX,
    MMIO_IDX,
    PERF_IDX,
    INSTR_IDX,
    DEBUG_IDX,   //debugger module index
    LAST_IDX
  } rule_idx_t;

  localparam rule_addr_t BASE_ADDR = 32'h1c000000;
  localparam rule_addr_t HWPE_ADDR_BASE_BIT = 20;

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
  localparam rule_addr_t IMEM_ADDR = 32'h00100000;
  localparam int unsigned IMEM_SIZE = 32'h08000;
  localparam rule_addr_t DMEM_ADDR = 32'h00110000;
  localparam int unsigned DMEM_SIZE = 32'h30000;
  localparam rule_addr_t SMEM_ADDR = 32'h00140000;
  localparam int unsigned SMEM_SIZE = 32'h30000;
  localparam int unsigned GMEM_SIZE = SMEM_ADDR + SMEM_SIZE - IMEM_ADDR;
  //  see reset vector in cv32e40p/bsp/crt0.S
  localparam rule_addr_t BOOT_ADDR = 32'h00100080;
  localparam rule_addr_t PERI_ADDR = 32'h00001000;
  //see cv32e40p/bsp/simple_system_regs.h
  localparam rule_addr_t MMIO_ADDR = 32'h80000000;
  localparam rule_addr_t MMADDR_EXIT = MMIO_ADDR + 32'h0;
  localparam rule_addr_t MMADDR_PRINT = MMIO_ADDR + 32'h4;
  localparam rule_addr_t MMADDR_PERF = MMIO_ADDR + 32'h8;
  //debugger module
  localparam rule_addr_t DEBUG_ADDR = 32'h1A11_0000;
  localparam int unsigned DEBUG_SIZE = 32'h0000_1000;

  typedef struct packed {
    rule_idx_t  idx;
    rule_addr_t start_addr;
    rule_addr_t end_addr;
  } tb_rule_t;

  localparam int unsigned NoRules = 6;
  localparam int unsigned NoIndices = LAST_IDX;
  // 
  localparam tb_rule_t [NoRules-1:0] addr_map = '{
      '{idx: PERIPH_IDX, start_addr: PERI_ADDR, end_addr: IMEM_ADDR},
      '{idx: DATA_IDX, start_addr: DMEM_ADDR, end_addr: DMEM_ADDR + DMEM_SIZE},
      '{idx: STACK_IDX, start_addr: SMEM_ADDR, end_addr: SMEM_ADDR + SMEM_SIZE},
      '{idx: MMIO_IDX, start_addr: MMIO_ADDR, end_addr: MMADDR_PERF},
      '{idx: PERF_IDX, start_addr: MMADDR_PERF, end_addr: MMADDR_PERF + DMEM_SIZE},
      '{idx: DEBUG_IDX, start_addr: DEBUG_ADDR, end_addr: DEBUG_ADDR + DEBUG_SIZE}
  };


  typedef logic [1:0] idx2b_t;
  typedef struct packed {
    idx2b_t idx;
    rule_addr_t start_addr;
    rule_addr_t end_addr;
  } rom_rule_t;

  localparam rom_rule_t [1:0] rom_map = '{
      '{idx: 2'd1, start_addr: DEBUG_ADDR, end_addr: DEBUG_ADDR + DEBUG_SIZE},
      '{idx: 2'd2, start_addr: IMEM_ADDR, end_addr: IMEM_ADDR + IMEM_SIZE}

  };

  localparam rom_rule_t [1:0] dm_sys_map = '{
      '{idx: 2'd1, start_addr: DMEM_ADDR, end_addr: DMEM_ADDR + DMEM_SIZE},
      '{idx: 2'd2, start_addr: IMEM_ADDR, end_addr: IMEM_ADDR + IMEM_SIZE}

  };


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

  //
  // jtag openocd bridge signals
  logic        sim_jtag_tck;
  logic        sim_jtag_tms;
  logic        sim_jtag_tdi;
  logic        sim_jtag_trstn;
  logic        sim_jtag_tdo;
  logic [31:0] sim_jtag_exit;
  logic        sim_jtag_enable;

  isolde_tcdm_if tcdm_debug_dmi ();
  isolde_tcdm_if tcdm_debug_sbus ();
  isolde_tcdm_if tcdm_debug_dmem ();
  isolde_tcdm_if tcdm_debug_imem ();
  jtag_pkg::jtag_req_t jtag_in;
  jtag_pkg::jtag_rsp_t jtag_out;
  logic [rv_dm_pkg::NrHarts-1:0] debug_req;


  localparam bit JTAG_BOOT = 1;
  localparam int unsigned OPENOCD_PORT = 9999;
  localparam CLUSTER_ID = 6'd0;
  localparam CORE_ID = 4'd0;

  localparam CORE_MHARTID = {21'b0, CLUSTER_ID, 1'b0, CORE_ID};
  localparam NrHarts = 1;
  localparam logic [NrHarts-1:0] SELECTABLE_HARTS = 1 << CORE_MHARTID;
  localparam HARTINFO = {8'h0, 4'h2, 3'b0, 1'b1, dm::DataCount, dm::DataAddr};
  //

  hwpe_stream_intf_tcdm tcdm[MP+1:0] (.clk(clk_i));

  isolde_tcdm_if tcdm_core_data ();
  isolde_tcdm_if tcdm_data_dm ();
  isolde_tcdm_if tcdm_data_dm_mux ();
  isolde_tcdm_if tcdm_stack ();
  isolde_tcdm_if tcdm_stack_shim ();

  isolde_tcdm_if tcdm_core_inst ();
  isolde_tcdm_if tcdm_inst_mem ();
  isolde_tcdm_if tcdm_inst_mem_mux ();
  isolde_tcdm_if tcdm_inst_dm ();
  isolde_tcdm_if tcdm_imem_shim ();

  logic [NC-1:0][ 1:0] evt;
  logic [MP-1:0]       tcdm_gnt;
  logic [MP-1:0][31:0] tcdm_r_data;
  logic [MP-1:0]       tcdm_r_valid;

  logic                core_sleep;
  logic fifo_full, fifo_empty;
  logic push_id_fifo, pop_id_fifo;
  rule_idx_t selected_idx, rsp_idx;


  assign push_id_fifo = ~fifo_full & tcdm_core_data.rsp.gnt;
  assign pop_id_fifo  = ~fifo_empty & tcdm_core_data.rsp.valid;

  always_ff @(posedge clk_i, negedge rst_ni)
    if (!rst_ni) begin
      rsp_idx <= INVALID;
    end


  addr_decode #(
      .NoIndices(NoIndices),    // number indices in rules
      .NoRules  (NoRules),      // total number of rules
      .addr_t   (rule_addr_t),  // address type
      .rule_t   (tb_rule_t)     // has to be overridden, see above!
  ) i_addr_decode_dut (
      .addr_i(tcdm_core_data.req.addr),  // address to decode
      .addr_map_i(addr_map),  // address map: rule with the highest position wins
      .idx_o(selected_idx),  // decoded index
      .dec_valid_o(),  // decode is valid
      .dec_error_o(),  // decode is not valid
      // Default index mapping enable
      .en_default_idx_i(1'b1),  // enable default port mapping
      .default_idx_i(INVALID)  // default port index
  );





  // Remember selected master for correct forwarding of read data/acknowledge.
  fifo_v3 #(
      .DATA_WIDTH(4),
      .DEPTH(4)
  ) i_id_fifo (
      .clk_i,
      .rst_ni,
      .flush_i(1'b0),
      .testmode_i(1'b0),
      .full_o(fifo_full),
      .empty_o(fifo_empty),
      .usage_o(),
      // Onehot mask.
      .data_i(selected_idx),
      .push_i(push_id_fifo),
      .data_o(rsp_idx),
      .pop_i(pop_id_fifo)
  );

  always_comb begin


    case (selected_idx)
      PERIPH_IDX: periph.req = tcdm_core_data.req.req;
      DATA_IDX:   tcdm[MP].req = tcdm_core_data.req.req;
      STACK_IDX: begin  //bind_stack
        tcdm_stack.req.req  = tcdm_core_data.req.req;
        tcdm_stack.req.addr = tcdm_core_data.req.addr;
        tcdm_stack.req.we   = tcdm_core_data.req.we;
        tcdm_stack.req.be   = tcdm_core_data.req.be;
        tcdm_stack.req.data = tcdm_core_data.req.data;
      end
      MMIO_IDX:   mmio_req = tcdm_core_data.req.req;
      PERF_IDX:   perfcnt_req = tcdm_core_data.req.req;
      DEBUG_IDX: begin  //bind_debug module
        tcdm_data_dm.req.req  = tcdm_core_data.req.req;
        tcdm_data_dm.req.addr = tcdm_core_data.req.addr;
        tcdm_data_dm.req.we   = tcdm_core_data.req.we;
        tcdm_data_dm.req.be   = tcdm_core_data.req.be;
        tcdm_data_dm.req.data = tcdm_core_data.req.data;
      end

    endcase


  end

  always_comb begin
    tcdm_core_data.rsp.gnt = '0;
    if (tcdm_core_data.req.req) begin
      case (selected_idx)
        PERIPH_IDX: tcdm_core_data.rsp.gnt = periph.gnt;
        DATA_IDX: tcdm_core_data.rsp.gnt = tcdm[MP].gnt;
        STACK_IDX: tcdm_core_data.rsp.gnt = tcdm_stack.rsp.gnt;
        MMIO_IDX: tcdm_core_data.rsp.gnt = mmio_gnt;
        PERF_IDX: tcdm_core_data.rsp.gnt = perfcnt_gnt;
        DEBUG_IDX: tcdm_core_data.rsp.gnt = tcdm_data_dm.rsp.gnt;
        default: tcdm_core_data.rsp.gnt = '0;
      endcase
    end
  end

  assign tcdm_core_data.rsp.valid = periph.r_valid | tcdm_stack.rsp.valid | tcdm_data_dm.rsp.valid | tcdm[MP].r_valid | mmio_rvalid | perfcnt_rvalid;

  always_comb begin

    case (rsp_idx)
      PERIPH_IDX: tcdm_core_data.rsp.data = periph.r_data;
      DATA_IDX: tcdm_core_data.rsp.data = tcdm[MP].r_data;
      STACK_IDX: tcdm_core_data.rsp.data = tcdm_stack.rsp.data;
      MMIO_IDX: tcdm_core_data.rsp.data = mmio_rdata;
      PERF_IDX: tcdm_core_data.rsp.data = perfcnt_rdata;
      DEBUG_IDX: tcdm_core_data.rsp.data = tcdm_data_dm.rsp.data;
      default: tcdm_core_data.rsp.data = '0;
    endcase
  end


  isolde_mux_tcdm i_mux_1 (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i1(tcdm_inst_dm),
      .tcdm_slave_i2(tcdm_data_dm),
      .tcdm_master_o(tcdm_debug_dmi)
  );

  isolde_demux_tcdm #(
      .rule_addr_t(rule_addr_t),
      .tb_rule_t  (rom_rule_t)
  ) i_demux_1 (
      .clk_i,
      .rst_ni,
      .mem_map_i(rom_map),
      .tcdm_slave_i(tcdm_core_inst),
      .tcdm_master_o1(tcdm_inst_dm),
      .tcdm_master_o2(tcdm_inst_mem)
  );


  isolde_demux_tcdm #(
      .rule_addr_t(rule_addr_t),
      .tb_rule_t  (rom_rule_t),
      .rom_memory (0)
  ) i_demux_2 (
      .clk_i,
      .rst_ni,
      .mem_map_i(dm_sys_map),
      .tcdm_slave_i(tcdm_debug_sbus),
      .tcdm_master_o1(tcdm_data_dm_mux),
      .tcdm_master_o2(tcdm_debug_imem)
  );

  isolde_mux_tcdm i_mux_2 (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i1(tcdm_debug_imem),
      .tcdm_slave_i2(tcdm_inst_mem),
      .tcdm_master_o(tcdm_inst_mem_mux)
  );


  /*
**
*/

  // make jtag bridge work
  assign sim_jtag_enable = JTAG_BOOT;

  rv_dm #() i_rv_dm (
      .clk_i,
      .rst_ni,
      /// Debug Module Interface (DMI) slave port 
      .s_dmi(tcdm_debug_dmi),
      //.s_dmi(tcdm_inst_dm),
      /// System Bus master port
      .m_sbus(tcdm_debug_sbus),
      /// JTAG
      .jtag_in(jtag_in),
      .jtag_out(jtag_out),
      .debug_req_o(debug_req)
  );
  /*
**
*/
  // jtag calls from dpi
  SimJTAG #(
      .TICK_DELAY(1),
      .PORT(OPENOCD_PORT)
  ) i_sim_jtag (
      .clock          (clk_i),
      .reset          (~rst_ni),
      .enable         (sim_jtag_enable),
      .init_done      (rst_ni),
      .jtag_TCK       (jtag_in.tck),
      .jtag_TMS       (jtag_in.tms),
      .jtag_TDI       (jtag_in.tdi),
      .jtag_TRSTn     (jtag_in.trst_n),
      .jtag_TDO_data  (jtag_out.tdo),
      .jtag_TDO_driven(1'b1),
      .exit           (sim_jtag_exit)
  );

  always_comb begin : jtag_exit_handler
    if (sim_jtag_exit) $finish(2);  // print stats too
  end

  hci_core_intf #(.DW(DW)) redmule_tcdm (.clk(clk_i));
  hwpe_ctrl_intf_periph #(.ID_WIDTH(ID)) periph (.clk(clk_i));



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
          perfcnt_d.id <= tcdm_core_data.req.data;
          perfcnt_d.cycle_counter <= cycle_counter;
          perfcnt_d.dmem.cnt_wr <= tb_lca_system.i_dummy_dmemory.cnt_wr;
          perfcnt_d.dmem.cnt_rd <= tb_lca_system.i_dummy_dmemory.cnt_rd;
          perfcnt_d.imem.cnt_rd <= tb_lca_system.i_dummy_imemory.cnt_rd;
          perfcnt_d.stack_mem.cnt_wr <= tb_lca_system.i_dummy_stack_memory.cnt_wr;
          perfcnt_d.stack_mem.cnt_rd <= tb_lca_system.i_dummy_stack_memory.cnt_rd;
          //$display("LATCH @%t id=%d,cycle_counter=%d\n",$time, tcdm_core_data.req.data,cycle_counter);
        end
        DIFF: begin
          perfcnt_q.id <= perfcnt_d.id;
          perfcnt_q.cycle_counter <= (cycle_counter - perfcnt_d.cycle_counter);
          perfcnt_q.dmem.cnt_wr <= (tb_lca_system.i_dummy_dmemory.cnt_wr - perfcnt_d.dmem.cnt_wr);
          perfcnt_q.dmem.cnt_rd <= (tb_lca_system.i_dummy_dmemory.cnt_rd - perfcnt_d.dmem.cnt_rd);
          //
          perfcnt_q.imem.cnt_rd <= (tb_lca_system.i_dummy_imemory.cnt_rd - perfcnt_d.imem.cnt_rd);
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
    perfcnt_gnt = perfcnt_req;
    if (perfcnt_req && tcdm_core_data.req.we && (tcdm_core_data.req.addr == MMADDR_PERF)) begin
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
        if (~tcdm_core_data.req.we) begin
          case (tcdm_core_data.req.addr)
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

    periph.add  = tcdm_core_data.req.addr;
    periph.wen  = ~tcdm_core_data.req.we;
    periph.be   = tcdm_core_data.req.be;
    periph.data = tcdm_core_data.req.data;
    periph.id   = '0;
    //periph_r_valid = '0;
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


  assign tcdm[MP].add = tcdm_core_data.req.addr;
  assign tcdm[MP].wen = ~tcdm_core_data.req.we;
  assign tcdm[MP].be = tcdm_core_data.req.be;
  assign tcdm[MP].data = tcdm_core_data.req.data;










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
  ) i_imem_shim (
      .tcdm_slave_i (tcdm_inst_mem_mux),
      //.tcdm_slave_i (tcdm_core_intf[0]),
      .tcdm_master_o(tcdm_imem_shim)
  );

  tb_tcdm_mem #(
      .MEMORY_SIZE (GMEM_SIZE),
      .DELAY_CYCLES(IMEM_LATENCY)
  ) i_dummy_imemory (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(tcdm_imem_shim)
  );


  isolde_addr_shim #(
      .START_ADDR(SMEM_ADDR),  // Set start address
      .END_ADDR(SMEM_ADDR + SMEM_SIZE)  // Set end address
  ) i_stack_mem_shim (
      .tcdm_slave_i (tcdm_stack),
      //.tcdm_slave_i (tcdm_core_intf[0]),
      .tcdm_master_o(tcdm_stack_shim)
  );

  tb_tcdm_mem #(
      .MEMORY_SIZE(SMEM_SIZE)
  ) i_dummy_stack_memory (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(tcdm_stack_shim)
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
      .DmHaltAddr      (32'h1A11_0800),     //TODO make a param here
      .DmExceptionAddr (32'h1A11_0808)      //TODO make a param here
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
      .data_req_o       (tcdm_core_data.req.req),
      .data_gnt_i       (tcdm_core_data.rsp.gnt),
      .data_rvalid_i    (tcdm_core_data.rsp.valid),
      .data_addr_o      (tcdm_core_data.req.addr),
      .data_be_o        (tcdm_core_data.req.be),
      .data_we_o        (tcdm_core_data.req.we),
      .data_wdata_o     (tcdm_core_data.req.data),
      .data_wdata_intg_o(),
      .data_rdata_i     (tcdm_core_data.rsp.data),
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

      .debug_req_i        (debug_req[0]),
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
    $fwrite(fh, "[TB LCA] @ t=%0t - writes[imemory] =%d\n", $time,
            tb_lca_system.i_dummy_imemory.cnt_wr);
    $fwrite(fh, "[TB LCA] @ t=%0t - reads [imemory] =%d\n", $time,
            tb_lca_system.i_dummy_imemory.cnt_rd);
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

    $display("waiting for shutdown from OpenOCD");
    do @(posedge clk_i); while (!sim_jtag_exit);

    $finish;
  endtask

  /*
** The semantics of the r_valid signal are not well defined with respect to the usual TCDM protocol. In PULP clusters, r_valid will be asserted also after write transactions, not only in reads. 
** https://hwpe-doc.readthedocs.io/en/latest/protocols.html#hwpe-mem
** see also https://ibex-core.readthedocs.io/en/latest/03_reference/load_store_unit.html
**/



  always_comb begin
    mmio_gnt = mmio_req;
  end

  always_ff @(posedge clk_i) begin
    if (~rst_ni) begin
      cycle_counter <= '0;
      mmio_rvalid   <= 0;
    end else cycle_counter <= cycle_counter + 1;

    if (mmio_gnt) begin
      case (tcdm_core_data.req.addr)
        MMADDR_EXIT: begin
          if (tcdm_core_data.req.we) endSimulation(tcdm_core_data.req.data);
          else begin
            mmio_rdata  <= cycle_counter + 1;
            mmio_rvalid <= 1;
          end

        end
        MMADDR_PRINT:
        if (tcdm_core_data.req.we) begin
          $write("%c", tcdm_core_data.req.data);
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
      $readmemh(stim_instr, tb_lca_system.i_dummy_imemory.memory);
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
