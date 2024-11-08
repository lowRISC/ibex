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
  // parameters
  parameter int unsigned PROB_STALL = 0;
  parameter int unsigned NC = 1;
  parameter int unsigned ID = 10;
  parameter int unsigned DW = redmule_pkg::DATA_W;
  parameter int unsigned MP = DW / 32;
  parameter int unsigned MEMORY_SIZE = 1118496;
  parameter int unsigned STACK_MEMORY_SIZE = 192 * 1024;
  parameter int unsigned PULP_XPULP = 1;
  parameter int unsigned FPU = 0;
  parameter int unsigned PULP_ZFINX = 0;
  parameter logic [31:0] IMEM_ADDR = 32'h00100000;
  parameter logic [31:0] DMEM_ADDR = 32'h00110000;
  parameter logic [31:0] SMEM_ADDR = 32'h00140000;
  parameter logic [31:0] BOOT_ADDR = 32'h00100000;
  parameter logic [31:0] PERI_ADDR = 32'h00001000;
  parameter logic [31:0] MMIO_ADDR = 32'h80000000;
  //
  parameter logic [31:0] MMADDR_EXIT = MMIO_ADDR + 32'h0;
  parameter logic [31:0] MMADDR_PRINT = MMIO_ADDR + 32'h4;


  logic test_mode;
  logic [31:0] core_boot_addr;
  logic redmule_busy;

  //hwpe_stream_intf_tcdm instr[0:0] (.clk(clk_i));
  hwpe_stream_intf_tcdm stack[0:0] (.clk(clk_i));
  hwpe_stream_intf_tcdm tcdm[MP+1:0] (.clk(clk_i));

  logic [NC-1:0][ 1:0] evt;

  logic [MP-1:0]       tcdm_req;
  logic [MP-1:0]       tcdm_gnt;
  logic [MP-1:0][31:0] tcdm_add;
  logic [MP-1:0]       tcdm_wen;
  logic [MP-1:0][ 3:0] tcdm_be;
  logic [MP-1:0][31:0] tcdm_data;
  logic [MP-1:0][31:0] tcdm_r_data;
  logic [MP-1:0]       tcdm_r_valid;
  logic                tcdm_r_opc;
  logic                tcdm_r_user;

  logic                periph_req;
  logic                periph_gnt;
  logic [  31:0]       periph_add;
  logic                periph_wen;
  logic [   3:0]       periph_be;
  logic [  31:0]       periph_data;
  logic [ID-1:0]       periph_id;
  logic [  31:0]       periph_r_data;
  logic                periph_r_valid;
  logic [ID-1:0]       periph_r_id;

  logic                instr_req;
  logic                instr_gnt;
  logic                instr_rvalid;
  logic [  31:0]       instr_addr;
  logic [  31:0]       instr_rdata;

  logic                data_req;
  logic                data_gnt;
  logic                data_rvalid;
  logic                data_we;
  logic [   3:0]       data_be;
  logic [  31:0]       data_addr;
  logic [  31:0]       data_wdata;
  logic [  31:0]       data_rdata;
  logic                data_err;
  logic                core_sleep;

  logic [  31:0]       cycle_counter;
  logic                mmio_rvalid;
  logic [  31:0]       mmio_rdata;



  // bindings
  always_comb begin : bind_periph
    periph_req  = data_req & (data_addr >= PERI_ADDR) & (data_addr < IMEM_ADDR);
    periph_add  = data_addr;
    periph_wen  = ~data_we;
    periph_be   = data_be;
    periph_data = data_wdata;
    periph_id   = '0;
  end

  always_comb begin : bind_instrs
    tcdm[MP+1].req  = instr_req;
    tcdm[MP+1].add  = instr_addr;
    tcdm[MP+1].wen  = 1'b1;
    tcdm[MP+1].be   = '0;
    tcdm[MP+1].data = '0;
    instr_gnt    = tcdm[MP+1].gnt;
    instr_rdata  = tcdm[MP+1].r_data;
    instr_rvalid = tcdm[MP+1].r_valid;
  end

  always_comb begin : bind_stack
    stack[0].req  = data_req & (data_addr >= SMEM_ADDR) & (data_addr < SMEM_ADDR + 32'h30000);
    stack[0].add  = data_addr;
    stack[0].wen  = ~data_we;
    stack[0].be   = data_be;
    stack[0].data = data_wdata;
  end

  //logic other_r_valid;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) mmio_rvalid <= '0;
    else mmio_rvalid <= data_req & (data_addr >= MMIO_ADDR);
  end

  for (genvar ii = 0; ii < MP; ii++) begin : tcdm_binding
    assign tcdm[ii].req     = tcdm_req[ii];
    assign tcdm[ii].add     = tcdm_add[ii];
    assign tcdm[ii].wen     = tcdm_wen[ii];
    assign tcdm[ii].be      = tcdm_be[ii];
    assign tcdm[ii].data    = tcdm_data[ii];
    assign tcdm_gnt[ii]     = tcdm[ii].gnt;
    assign tcdm_r_data[ii]  = tcdm[ii].r_data;
    assign tcdm_r_valid[ii] = tcdm[ii].r_valid;
  end
  assign tcdm[MP].req = data_req & (data_addr >= DMEM_ADDR) & (data_addr < DMEM_ADDR + 32'h30000);
  assign tcdm[MP].add = data_addr;
  assign tcdm[MP].wen = ~data_we;
  assign tcdm[MP].be = data_be;
  assign tcdm[MP].data = data_wdata;
  assign tcdm_r_opc = 0;
  assign tcdm_r_user = 0;
  assign data_gnt    = periph_req ?
                       periph_gnt : stack[0].req ?
                                    stack[0].gnt : tcdm[MP].req ?
                                                   tcdm[MP].gnt : '1;
  assign data_rdata  = periph_r_valid ? periph_r_data  :
                                        stack[0].r_valid ? stack[0].r_data  :
                                                           tcdm[MP].r_valid ? tcdm[MP].r_data : 
                                                                                               mmio_rvalid ? mmio_rdata: '0;

  assign data_rvalid = periph_r_valid | stack[0].r_valid | tcdm[MP].r_valid | mmio_rvalid;

  redmule_wrap #(
      .ID_WIDTH(ID),
      .N_CORES (NC),
      .DW      (DW),
      .MP      (DW / 32)
  ) i_redmule_wrap (
      .clk_i           (clk_i),
      .rst_ni          (rst_ni),
      .test_mode_i     (test_mode),
      .evt_o           (evt),
      .busy_o          (redmule_busy),
      .tcdm_req_o      (tcdm_req),
      .tcdm_add_o      (tcdm_add),
      .tcdm_wen_o      (tcdm_wen),
      .tcdm_be_o       (tcdm_be),
      .tcdm_data_o     (tcdm_data),
      .tcdm_gnt_i      (tcdm_gnt),
      .tcdm_r_data_i   (tcdm_r_data),
      .tcdm_r_valid_i  (tcdm_r_valid),
      .tcdm_r_opc_i    (tcdm_r_opc),
      .tcdm_r_user_i   (tcdm_r_user),
      .periph_req_i    (periph_req),
      .periph_gnt_o    (periph_gnt),
      .periph_add_i    (periph_add),
      .periph_wen_i    (periph_wen),
      .periph_be_i     (periph_be),
      .periph_data_i   (periph_data),
      .periph_id_i     (periph_id),
      .periph_r_data_o (periph_r_data),
      .periph_r_valid_o(periph_r_valid),
      .periph_r_id_o   (periph_r_id)
  );

  tb_tcdm_verilator #(
      .MP         (MP + 2),
      .MEMORY_SIZE(MEMORY_SIZE),
      .BASE_ADDR  (IMEM_ADDR)
  ) i_dummy_memory (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .enable_i(1'b1),
      .tcdm    (tcdm)
  );

  tb_tcdm_verilator #(
      .MP         (1),
      .MEMORY_SIZE(32'h30000)
  ) i_dummy_stack_memory (
      .clk_i   (clk_i),
      .rst_ni  (rst_ni),
      .enable_i(1'b1),
      .tcdm    (stack)
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

      .hart_id_i  (32'b0),
      // First instruction executed is at 0x0 + 0x80
      .boot_addr_i(core_boot_addr),

      .instr_req_o   (instr_req),
      .instr_gnt_i   (instr_gnt),
      .instr_rvalid_i(instr_rvalid),
      .instr_addr_o  (instr_addr),
      .instr_rdata_i (instr_rdata),
      //.instr_rdata_intg_i     (instr_rdata_intg),
      //.instr_err_i            (instr_err),

      .data_req_o       (data_req),
      .data_gnt_i       (data_gnt),
      .data_rvalid_i    (data_rvalid),
      .data_we_o        (data_we),
      .data_be_o        (data_be),
      .data_addr_o      (data_addr),
      .data_wdata_o     (data_wdata),
      .data_wdata_intg_o(),
      .data_rdata_i     (data_rdata),
      .data_rdata_intg_i(),
      .data_err_i       (),

      .irq_software_i( evt[0][0]),
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
      .core_sleep_o          ()
  );

  // cv32e40p_core #(
  //     .PULP_XPULP(PULP_XPULP),
  //     .FPU       (FPU),
  //     .PULP_ZFINX(PULP_ZFINX)
  // ) i_cv32e40p_core (
  //     // Clock and Reset
  //     .clk_i(clk_i),
  //     .rst_ni(rst_ni),
  //     .pulp_clock_en_i(1'b1),  // PULP clock enable (only used if PULP_CLUSTER = 1)
  //     .scan_cg_en_i(1'b0),  // Enable all clock gates for testing
  //     // Core ID, Cluster ID, debug mode halt address and boot address are considered more or less static
  //     .boot_addr_i(core_boot_addr),
  //     .mtvec_addr_i('0),
  //     .dm_halt_addr_i('0),
  //     .hart_id_i('0),
  //     .dm_exception_addr_i('0),
  //     // Instruction memory interface
  //     .instr_req_o(instr_req),
  //     .instr_gnt_i(instr_gnt),
  //     .instr_rvalid_i(instr_rvalid),
  //     .instr_addr_o(instr_addr),
  //     .instr_rdata_i(instr_rdata),
  //     // Data memory interface
  //     .data_req_o(data_req),
  //     .data_gnt_i(data_gnt),
  //     .data_rvalid_i(data_rvalid),
  //     .data_we_o(data_we),
  //     .data_be_o(data_be),
  //     .data_addr_o(data_addr),
  //     .data_wdata_o(data_wdata),
  //     .data_rdata_i(data_rdata),
  //     // apu-interconnect
  //     // handshake signals
  //     .apu_req_o(),
  //     .apu_gnt_i('0),
  //     // request channel
  //     .apu_operands_o(),
  //     .apu_op_o(),
  //     .apu_flags_o(),
  //     // response channel
  //     .apu_rvalid_i('0),
  //     .apu_result_i('0),
  //     .apu_flags_i('0),
  //     // Interrupt inputs
  //     .irq_i({28'd0, evt[0][0], 3'd0}),  // CLINT interrupts + CLINT extension interrupts
  //     .irq_ack_o(),
  //     .irq_id_o(),
  //     // Debug Interface
  //     .debug_req_i('0),
  //     .debug_havereset_o(),
  //     .debug_running_o(),
  //     .debug_halted_o(),
  //     // CPU Control Signals
  //     .fetch_enable_i(fetch_enable_i),
  //     .core_sleep_o(core_sleep)
  // );


  initial begin : load_prog
    automatic string firmware;



    if ($value$plusargs("firmware=%s", firmware)) begin

      $display("[TESTBENCH] @ t=%0t: loading firmware %0s", $time, firmware);
      // load instruction memory
      $readmemh(firmware, tb_lca_system.i_dummy_memory.memory);
    end else begin
      $display("No firmware specified");
      $finish;
    end

    core_boot_addr = BOOT_ADDR;
  end



  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) cycle_counter <= '0;
    else cycle_counter <= cycle_counter + 1;

    if ((data_addr == MMADDR_EXIT) && data_req) begin
      if (data_we) errors <= data_wdata;
      else mmio_rdata <= cycle_counter;
    end
    if ((data_addr == MMADDR_PRINT) && (data_we & data_req)) begin
      $write("%c", data_wdata[7:0]);
    end
  end

  int errors = -1;
  initial begin
    test_mode = 1'b0;

    do @(posedge clk_i); while (~core_sleep || errors == -1);

    $display("[TB] - errors=%08x", errors);
    if (errors != 0) begin
      $error("[TB] - Fail!");
    end else begin
      $display("[TB] - Success!");
    end
    $finish;

  end

endmodule  // tb_lca_system
