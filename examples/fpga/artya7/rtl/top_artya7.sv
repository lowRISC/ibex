// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_artya7 (
    input               IO_CLK,
    input               IO_RST_N,
    output [3:0]        LED,

    input               JTAG_TCK,
    input               JTAG_TMS,
    input               JTAG_TRST_N,
    input               JTAG_TDI,
    output              JTAG_TDO,
    input               JTAG_RESET_N
);

  parameter int          MEM_SIZE     = 64 * 1024; // 64 kB
  parameter logic [31:0] MEM_START    = 32'h00000000;
  parameter logic [31:0] MEM_MASK     = MEM_SIZE-1;
  parameter              SRAMInitFile = "";

  parameter logic [31:0] DEBUG_START  = 32'h 1a110000;
  parameter int          DEBUG_SIZE   = 64 * 1024; // 64 kB
  parameter logic [31:0] DEBUG_MASK   = DEBUG_SIZE-1;

  // debug functionality is optional
  localparam DBG = 1;
  localparam int unsigned DbgHwBreakNum = (DBG == 1) ? 2 : 0;
  localparam bit DbgTriggerEn = (DBG == 1) ? 1'b1 : 1'b0;

  logic clk_sys, rst_sys_n, rst_core_n;

  // Ibex instruction host bus
  logic        instr_req;
  logic        instr_gnt;
  logic        instr_rvalid;
  logic [31:0] instr_addr;

  // Ibex data host bus
  logic        data_req;
  logic        data_gnt;
  logic        data_rvalid;
  logic        data_we;
  logic  [3:0] data_be;
  logic [31:0] data_addr;
  logic [31:0] data_wdata;

  // debug unit host interface
  logic        dumi_req;
  logic        dumi_gnt;
  logic        dumi_rvalid;
  logic [31:0] dumi_addr;
  logic        dumi_we;
  logic [31:0] dumi_wdata;
  logic  [3:0] dumi_be;

  // shared system bus (arbitrated between Ibex instr, Ibex data, and debug)
  logic        ssb_req;
  logic [31:0] ssb_addr;
  logic        ssb_we;
  logic [31:0] ssb_wdata;
  logic  [3:0] ssb_be;
  logic [31:0] ssb_rdata;

  // addressed devices on shared system bus
  logic [31:0] ssb_rdata_debug;
  logic [31:0] ssb_rdata_sram;
  logic        ssb_req_sram, ssb_req_debug;
  logic        ssb_device_sram, ssb_device_debug;

  logic        ndmreset_req;
  logic        dm_debug_req;

  ibex_core #(
     .RegFile(ibex_pkg::RegFileFPGA),
     .DbgTriggerEn(DbgTriggerEn),
     .DbgHwBreakNum(DbgHwBreakNum),
     .DmHaltAddr(DEBUG_START + dm::HaltAddress),
     .DmExceptionAddr(DEBUG_START + dm::ExceptionAddress)
  ) u_core (
     .clk_i                 (clk_sys),
     .rst_ni                (rst_core_n),

     .test_en_i             ('b0),

     .hart_id_i             (32'b0),
     // First instruction executed is at 0x0 + 0x80
     .boot_addr_i           (32'h00000000),

     .instr_req_o           (instr_req),
     .instr_gnt_i           (instr_gnt),
     .instr_rvalid_i        (instr_rvalid),
     .instr_addr_o          (instr_addr),
     .instr_rdata_i         (ssb_rdata),
     .instr_err_i           ('b0),

     .data_req_o            (data_req),
     .data_gnt_i            (data_gnt),
     .data_rvalid_i         (data_rvalid),
     .data_we_o             (data_we),
     .data_be_o             (data_be),
     .data_addr_o           (data_addr),
     .data_wdata_o          (data_wdata),
     .data_rdata_i          (ssb_rdata),
     .data_err_i            ('b0),

     .irq_software_i        (1'b0),
     .irq_timer_i           (1'b0),
     .irq_external_i        (1'b0),
     .irq_fast_i            (15'b0),
     .irq_nm_i              (1'b0),

     .debug_req_i           (dm_debug_req),

     .fetch_enable_i        ('b1),
     .alert_minor_o         (),
     .alert_major_o         (),
     .core_sleep_o          ()
  );

  // arbitrate between the three would-be bus hosts
  always_comb begin
    ssb_addr       = 32'b0;
    ssb_we         = 1'b0;
    ssb_be         = 4'b0;
    ssb_wdata      = 32'b0;
    dumi_gnt       = 1'b0;
    instr_gnt      = 1'b0;
    data_gnt       = 1'b0;
    if (dumi_req) begin
      ssb_we         = dumi_we;
      ssb_be         = dumi_be;
      ssb_addr       = dumi_addr;
      ssb_wdata      = dumi_wdata;
      dumi_gnt       = 1'b1;
    end else if (instr_req) begin
      ssb_addr       = instr_addr;
      instr_gnt      = 1'b1;
    end else if (data_req) begin
      ssb_we         = data_we;
      ssb_be         = data_be;
      ssb_addr       = data_addr;
      ssb_wdata      = data_wdata;
      data_gnt       = 1'b1;
    end
  end

  assign ssb_req = dumi_req | instr_req | data_req;

  // SRAM block for instruction and data storage
  ram_1p #(
    .Depth(MEM_SIZE / 4),
    .MemInitFile(SRAMInitFile)
  ) u_ram (
    .clk_i     ( clk_sys        ),
    .rst_ni    ( rst_sys_n      ),
    .req_i     ( ssb_req_sram   ),
    .we_i      ( ssb_we         ),
    .be_i      ( ssb_be         ),
    .addr_i    ( ssb_addr       ),
    .wdata_i   ( ssb_wdata      ),
    .rvalid_o  (),
    .rdata_o   ( ssb_rdata_sram )
  );

  // decode which device is being addressed
  
  always @(posedge clk_sys, negedge rst_sys_n)
  begin
    if (~rst_sys_n)
    begin
      ssb_device_debug <= 1'b0;
      ssb_device_sram  <= 1'b0;
    end else begin
      ssb_device_debug <= ssb_req_debug;
      ssb_device_sram  <= ssb_req_sram;
    end
  end

  assign ssb_req_sram  = ((ssb_addr & ~MEM_MASK) == MEM_START) && ssb_req;
  assign ssb_req_debug = ((ssb_addr & ~DEBUG_MASK) == DEBUG_START) && ssb_req;

  assign ssb_rdata = ( {32{ssb_device_debug}} & ssb_rdata_debug ) |
                     ( {32{ssb_device_sram}}  & ssb_rdata_sram  );

  always @(posedge clk_sys, negedge rst_sys_n)
  begin
    if (~rst_sys_n)
    begin
      instr_rvalid <= 1'b0;
      data_rvalid  <= 1'b0;
      dumi_rvalid  <= 1'b0;
    end else begin
      instr_rvalid <= instr_gnt;
      data_rvalid  <= data_gnt;
      dumi_rvalid  <= dumi_gnt;
    end
  end

  // Connect the LED output to the lower four bits of the most significant
  // byte
  logic [3:0] leds;
  always_ff @(posedge clk_sys or negedge rst_sys_n) begin
    if (!rst_sys_n) begin
      leds <= 4'b0;
    end else begin
      if (ssb_req_sram && data_req && data_we) begin
        for (int i = 0; i < 4; i = i + 1) begin
          if (data_be[i] == 1'b1) begin
            leds <= data_wdata[i*8 +: 4];
          end
        end
      end
    end
  end
  assign LED = leds;

  // Clock and reset
  clkgen_xil7series
    clkgen(
      .IO_CLK,
      .IO_RST_N,
      .clk_sys,
      .rst_sys_n
    );

  assign rst_core_n = rst_sys_n & JTAG_RESET_N & ~ndmreset_req;

  // Manufacturers must replace this code with one of their own IDs.
  // Field structure as defined in the IEEE 1149.1 (JTAG) specification,
  // section 12.1.1.
  localparam logic [31:0] JTAG_IDCODE = {
    4'h0,     // Version
    16'h4942, // Part Number: "IB"
    11'h426,  // Manufacturer Identity: Google
    1'b1      // (fixed)
  };

  // instantiate debug unit

  jtag_pkg::jtag_req_t jtag_req;
  jtag_pkg::jtag_rsp_t jtag_rsp;
  logic unused_jtag_tdo_oe_o;

  assign jtag_req.tck    = JTAG_TCK;
  assign jtag_req.tms    = JTAG_TMS;
  assign jtag_req.trst_n = JTAG_TRST_N;
  assign jtag_req.tdi    = JTAG_TDI;
  assign JTAG_TDO        = jtag_rsp.tdo;
  assign unused_jtag_tdo_oe_o = jtag_rsp.tdo_oe;

  generate
  if (DBG == 1) begin
    dm_top #(
      .NrHarts       (1),
      .IdcodeValue   (JTAG_IDCODE)
    ) u_dm_top (
      .clk_i         (clk_sys),
      .rst_ni        (rst_sys_n),
      .testmode_i    (1'b0),
      .ndmreset_o    (ndmreset_req),
      .dmactive_o    (),
      .debug_req_o   (dm_debug_req),
      .unavailable_i (1'b0),

      // bus device with debug memory (for execution-based debug)
      .slave_req_i       ( ssb_req_debug     ),
      .slave_we_i        ( ssb_we            ),
      .slave_addr_i      ( ssb_addr          ),
      .slave_be_i        ( ssb_be            ),
      .slave_wdata_i     ( ssb_wdata         ),
      .slave_rdata_o     ( ssb_rdata_debug   ),

      // bus host (for system bus accesses, SBA)
      .master_req_o      ( dumi_req          ),
      .master_add_o      ( dumi_addr         ),
      .master_we_o       ( dumi_we           ),
      .master_wdata_o    ( dumi_wdata        ),
      .master_be_o       ( dumi_be           ),
      .master_gnt_i      ( dumi_gnt          ),
      .master_r_valid_i  ( dumi_rvalid       ),
      .master_r_rdata_i  ( ssb_rdata         ),

      //JTAG
      .jtag_req_i    (jtag_req),
      .jtag_rsp_o    (jtag_rsp)
    );
  end
  if (DBG == 0) begin
    assign dm_debug_req = 1'b0;
    assign ndmreset_req = 1'b0;
    assign dumi_req = 1'b0;
    assign dumi_addr = 32'h0;
    assign dumi_we = 1'b0;
    assign dumi_wdata = 32'h0;
    assign dumi_be = 4'b0;
    assign ssb_rdata_debug = 32'h0;
  end
  endgenerate

endmodule
