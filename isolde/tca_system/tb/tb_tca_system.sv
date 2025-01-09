// Copyleft 2024 ISOLDE
// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Yvan Tortorella <yvan.tortorella@unibo.it>
//

timeunit 1ps; timeprecision 1ps;

module tb_tca_system (
    input logic clk_i,
    input logic rst_ni,
    input logic fetch_enable_i
);

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
//
  //localparam int unsigned IMEM_LATENCY = 0;
  parameter int unsigned IMEM_LATENCY = 0;
  // REDMULE parameters
  import redmule_pkg::*;
  localparam int unsigned PROB_STALL = 0;
  localparam int unsigned NC = 1;
  localparam int unsigned ID = isolde_cv_x_if_pkg::X_ID_WIDTH;
  localparam int unsigned DW = redmule_pkg::DATA_W;
  localparam int unsigned MP = DW / 32;
  localparam int unsigned MEMORY_SIZE = 32'h30000;
  localparam int unsigned STACK_MEMORY_SIZE = 32'h30000;
  localparam int unsigned PULP_XPULP = 1;
  localparam int unsigned FPU = 0;
  localparam int unsigned PULP_ZFINX = 0;
  localparam logic [31:0] BASE_ADDR = 32'h1c000000;
  localparam logic [31:0] HWPE_ADDR_BASE_BIT = 20;

  int fh;  //filehandle
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
  //  see reset vector in cv32e40p/bsp/crt0.S
  localparam logic [31:0] BOOT_ADDR = 32'h00100080;
  //see cv32e40p/bsp/simple_system_regs.h
  localparam logic [31:0] MMIO_ADDR = 32'h80000000;
  localparam logic [31:0] MMADDR_EXIT = MMIO_ADDR + 32'h0;
  localparam logic [31:0] MMADDR_PRINT = MMIO_ADDR + 32'h4;
  localparam logic [31:0] MMADDR_PERF = MMIO_ADDR + 32'h8;

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

  //hwpe_stream_intf_tcdm instr[0:0] (.clk(clk_i));
  hwpe_stream_intf_tcdm stack[0:0] (.clk(clk_i));
  hwpe_stream_intf_tcdm tcdm[MP+1:0] (.clk(clk_i));

  logic [NC-1:0][ 1:0] evt;
  logic [MP-1:0]       tcdm_gnt;
  logic [MP-1:0][31:0] tcdm_r_data;
  logic [MP-1:0]       tcdm_r_valid;

  logic                core_sleep;

  typedef struct  {
    logic        req;
    logic [31:0] addr;
  } core_inst_req_t;

  typedef struct  {
    logic        gnt;
    logic        valid;
    logic [31:0] data;
  } core_inst_rsp_t;

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

  core_inst_req_t core_inst_req;
  core_inst_rsp_t core_inst_rsp;

  core_data_req_t core_data_req;
  core_data_rsp_t core_data_rsp;

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
          perfcnt_d.dmem.cnt_wr <= tb_tca_system.i_dummy_dmemory.cnt_wr;
          perfcnt_d.dmem.cnt_rd <= tb_tca_system.i_dummy_dmemory.cnt_rd;
          perfcnt_d.imem.cnt_rd <= tb_tca_system.i_dummy_imemory.cnt_rd;
          perfcnt_d.stack_mem.cnt_wr <= tb_tca_system.i_dummy_stack_memory.cnt_wr;
          perfcnt_d.stack_mem.cnt_rd <= tb_tca_system.i_dummy_stack_memory.cnt_rd;
          //$display("LATCH @%t id=%d,cycle_counter=%d\n",$time, core_data_req.data,cycle_counter);
        end
        DIFF: begin
          perfcnt_q.id <= perfcnt_d.id;
          perfcnt_q.cycle_counter <= (cycle_counter - perfcnt_d.cycle_counter);
          perfcnt_q.dmem.cnt_wr <= (tb_tca_system.i_dummy_dmemory.cnt_wr - perfcnt_d.dmem.cnt_wr);
          perfcnt_q.dmem.cnt_rd <= (tb_tca_system.i_dummy_dmemory.cnt_rd - perfcnt_d.dmem.cnt_rd);
          //
          perfcnt_q.imem.cnt_rd <= (tb_tca_system.i_dummy_imemory.cnt_rd - perfcnt_d.imem.cnt_rd);
          //
          perfcnt_q.stack_mem.cnt_wr <= (tb_tca_system.i_dummy_stack_memory.cnt_wr-perfcnt_d.stack_mem.cnt_wr);
          perfcnt_q.stack_mem.cnt_rd <= (tb_tca_system.i_dummy_stack_memory.cnt_rd-perfcnt_d.stack_mem.cnt_rd);

          //$display("DIFF @%t id=%d,cycle_counter=%h\n",$time,  perfcnt_d.id, cycle_counter);
        end
        PRINT: begin
          $display("PRINT @%t id=%d,cycles =%d\n", $time, perfcnt_q.id, perfcnt_q.cycle_counter);
          // $display("[TB TCA] @ t=%0t - writes[imemory] =%d", $time, tb_tca_system.i_dummy_imemory.cnt_wr);
          $display("[TB TCA] @ t=%0t - reads [imemory] =%d", $time, perfcnt_q.imem.cnt_rd);
          //
          $display("[TB TCA] @ t=%0t - writes[dmemory] =%d", $time, perfcnt_q.dmem.cnt_wr);
          $display("[TB TCA] @ t=%0t - reads [dmemory] =%d", $time, perfcnt_q.dmem.cnt_rd);
          //
          $display("[TB TCA] @ t=%0t - writes[stack] =%d", $time, perfcnt_q.stack_mem.cnt_wr);
          $display("[TB TCA] @ t=%0t - reads [stack] =%d", $time, perfcnt_q.stack_mem.cnt_rd);
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

  // bindings


  always_comb begin : bind_instrs
    tcdm[MP+1].req = core_inst_req.req;
    tcdm[MP+1].add = core_inst_req.addr;
    tcdm[MP+1].wen = 1'b1;
    tcdm[MP+1].be = '0;
    tcdm[MP+1].data = '0;
    core_inst_rsp.gnt = tcdm[MP+1].gnt;
    core_inst_rsp.valid = tcdm[MP+1].r_valid;
    core_inst_rsp.data = tcdm[MP+1].r_data;
  end

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

  assign core_data_rsp.gnt =  stack[0].req ?
                                          stack[0].gnt : tcdm[MP].req ?
                                                   tcdm[MP].gnt : mmio_req ?
                                                                  mmio_gnt : perfcnt_req ?
                                                                             perfcnt_gnt : '1;

  assign core_data_rsp.data = stack[0].r_valid ? stack[0].r_data  :
                                                 tcdm[MP].r_valid ? tcdm[MP].r_data :
                                                                    mmio_rvalid ? mmio_rdata:  
                                                                                  perfcnt_rvalid ? perfcnt_rdata :'0;
  assign core_data_rsp.valid =  stack[0].r_valid | tcdm[MP].r_valid | mmio_rvalid | perfcnt_rvalid;






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


  tb_tcdm_verilator #(
      .MP         (1),
      .MEMORY_SIZE(GMEM_SIZE),
      .BASE_ADDR  (IMEM_ADDR),
      .DELAY_CYCLES(IMEM_LATENCY)
  ) i_dummy_imemory (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .enable_i(1'b1),
      .tcdm    (tcdm[MP+1:MP+1])
  );

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
      .DmHaltAddr      (32'h00100000),
      .DmExceptionAddr (32'h00100000)
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
      .instr_req_o      (core_inst_req.req),
      .instr_gnt_i      (core_inst_rsp.gnt),
      .instr_rvalid_i   (core_inst_rsp.valid),
      .instr_addr_o     (core_inst_req.addr),
      .instr_rdata_i    (core_inst_rsp.data),
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

      .debug_req_i        (1'b0),
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
      .core_xif      (core_xif)
  );




  // Declare the task with an input parameter for errors
  task endSimulation(input int errors);
    if (errors != 0) begin
      $display("[TB TCA] @ t=%0t - Fail!", $time);
      //      $error("[TB TCA] @ t=%0t - errors=%08x", $time, errors);
      $display("[TB TCA] @ t=%0t - errors=%08x", $time, errors);
    end else begin
      $display("[TB TCA] @ t=%0t - Success!", $time);
      $display("[TB TCA] @ t=%0t - errors=%08x", $time, errors);
    end
    $fwrite(fh, "[TB TCA] @ t=%0t - writes[imemory] =%d\n", $time,
            tb_tca_system.i_dummy_imemory.cnt_wr);
    $fwrite(fh, "[TB TCA] @ t=%0t - reads [imemory] =%d\n", $time,
            tb_tca_system.i_dummy_imemory.cnt_rd);
    //
    $fwrite(fh, "[TB TCA] @ t=%0t - writes[dmemory] =%d\n", $time,
            tb_tca_system.i_dummy_dmemory.cnt_wr);
    $fwrite(fh, "[TB TCA] @ t=%0t - reads [dmemory] =%d\n", $time,
            tb_tca_system.i_dummy_dmemory.cnt_rd);
    //
    $fwrite(fh, "[TB TCA] @ t=%0t - writes[stack] =%d\n", $time,
            tb_tca_system.i_dummy_stack_memory.cnt_wr);
    $fwrite(fh, "[TB TCA] @ t=%0t - reads [stack] =%d\n", $time,
            tb_tca_system.i_dummy_stack_memory.cnt_rd);
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
    // Load instruction and data memory
    if (!$value$plusargs("STIM_INSTR=%s", stim_instr)) begin
      $display("No STIM_INSTR specified");
      $finish;
    end else begin
      $display("[TESTBENCH] @ t=%0t: loading %0s into imemory", $time, stim_instr);
      $readmemh(stim_instr, tb_tca_system.i_dummy_imemory.memory);
    end

    if (!$value$plusargs("STIM_DATA=%s", stim_data)) begin
      $display("No STIM_DATA specified");
      $finish;
    end else begin
      $display("[TESTBENCH] @ t=%0t: loading %0s into dmemory", $time, stim_data);
      $readmemh(stim_data, tb_tca_system.i_dummy_dmemory.memory);
    end

    test_mode = 1'b0;

  end

  // close output file for writing
  final begin

    $fclose(fh);

  end
endmodule  // tb_tca_system
