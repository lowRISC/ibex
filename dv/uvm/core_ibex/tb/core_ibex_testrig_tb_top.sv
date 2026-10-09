// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define BOOT_ADDR 32'h8000_0000

module core_ibex_testrig_tb_top;
  import ibex_pkg::*;
  import ibex_cheriot_pkg::*;

  wire clk;
  wire rst_n;

  clk_rst_if clk_if(.clk(clk), .rst_n(rst_n));
  core_ibex_dii_intf dii_if(.clk(clk), .rst_n(rst_n), .rvfi_valid(dut.rvfi_valid));
  core_ibex_rvfi_if rvfi_if(.clk(clk));

  // Reply to revoker with zeros always
  logic        trvk_revbm_req;
  logic        trvk_revbm_rvalid_q;
  logic [38:0] trvk_revbm_rdata_intg_zero;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) trvk_revbm_rvalid_q <= 1'b0;
    else        trvk_revbm_rvalid_q <= trvk_revbm_req;
  end

  prim_secded_inv_39_32_enc u_trvk_revbm_word_enc (
    .data_i (32'b0),
    .data_o (trvk_revbm_rdata_intg_zero)
  );

  localparam int unsigned RamDepth = 8192*1024/4;
  localparam int unsigned RamAddrW = $clog2(RamDepth);

  logic instr_req;
  logic instr_gnt;
  logic instr_rvalid;

  logic        data_req;
  logic        data_gnt;
  logic        data_rvalid;
  logic        data_we;
  logic [3:0]  data_be;
  logic [31:0] data_addr;
  logic [31:0] data_wdata;
  logic        data_tag_wr;
  logic [31:0] data_rdata;
  logic        data_tag_rd;
  logic [6:0]  data_rdata_intg;
  logic        data_is_cap;
  logic        data_err;

  ibex_top_tracing #(
    .PMPEnable        ( 1'b0                   ),
    .PMPGranularity   ( 0                      ),
    .PMPNumRegions    ( 4                      ),
    .MHPMCounterNum   ( 0                      ),
    .MHPMCounterWidth ( 40                     ),
    .RV32E            ( 1'b1                   ),
    .RV32M            ( RV32MFast              ),
    .RV32B            ( RV32BNone              ),
    .RV32ZC           ( RV32Zca                ),
    .RegFile          ( RegFileFF              ),
    .BranchTargetALU  ( 1'b1                   ),
    .ICache           ( 1'b0                   ),
    .ICacheECC        ( 1'b0                   ),
    .BranchPredictor  ( 1'b0                   ),
    .DbgTriggerEn     ( 1'b0                   ),
    .DbgHwBreakNum    ( 1                      ),
    .WritebackStage   ( 1'b1                   ),
    .SecureIbex       ( 1'b0                   ),
    .LockstepOffset   ( 1                      ),
    .MemECC           ( 1'b0                   ),
    .MemDataWidth     ( 32                     ),
    .ICacheScramble   ( 1'b0                   ),
    .RndCnstLfsrSeed  ( RndCnstLfsrSeedDefault ),
    .RndCnstLfsrPerm  ( RndCnstLfsrPermDefault ),
    /* Debug module addresses adapted from cheriot-ibex ibex_top_sram.sv
     * (and ibex_top.sv) just in case they matter to TestRIG/Sail.
     * In any event, they should stand out in a waveform/trace.
     **/
    .DmBaseAddr       ( 32'h1A110000           ),
    .DmAddrMask       ( 32'h00000FFF           ),
    .DmHaltAddr       ( 32'h1A110800           ),
    .DmExceptionAddr  ( 32'h1A110808           ),
    .BaseIsa          ( BaseIsaRV32IorCHERIoT  )
  ) dut (
    .clk_i                     (clk),
    .rst_ni                    (rst_n),

    .test_en_i                 (1'b1),
    .scan_rst_ni               (1'b1),
    .ram_cfg_icache_tag_i      (prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT),
    .ram_cfg_icache_tag_o      (),
    .ram_cfg_icache_data_i     (prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT),
    .ram_cfg_icache_data_o     (),

    .cheriot_enable_i          (ibex_pkg::IbexMuBiOn),
    .mcounteren_writable_i     (ibex_pkg::IbexMuBiOn),

    // Revocation-bitmap (TRVK) port tied off since TestRIG doesn't yet model the revocation
    .trvk_heap_base_addr_i     (32'b0),
    .trvk_revbm_req_o          (trvk_revbm_req),
    .trvk_revbm_gnt_i          (trvk_revbm_req),
    .trvk_revbm_rvalid_i       (trvk_revbm_rvalid_q),
    .trvk_revbm_addr_o         (),
    .trvk_revbm_rdata_i        (32'b0),
    .trvk_revbm_rdata_intg_i   (trvk_revbm_rdata_intg_zero[38:32]),
    .trvk_revbm_err_i          (1'b0),

    .hart_id_i                 ('0),
    .boot_addr_i               (`BOOT_ADDR), // align with spike boot address

    .instr_req_o               (instr_req),
    .instr_gnt_i               (instr_gnt),
    .instr_rvalid_i            (instr_rvalid),
    .instr_addr_o              (),
    .instr_rdata_i             ('0),
    .instr_rdata_intg_i        ('0),
    .instr_err_i               (1'b0),

    .data_req_o                (data_req),
    .data_gnt_i                (data_gnt),
    .data_rvalid_i             (data_rvalid),
    .data_we_o                 (data_we),
    .data_be_o                 (data_be),
    .data_addr_o               (data_addr),
    .data_wdata_o              (data_wdata),
    .data_tag_o                (data_tag_wr),
    .data_wdata_intg_o         (),
    .data_rdata_i              (data_rdata),
    .data_tag_i                (data_tag_rd),
    .data_rdata_intg_i         ('0),
    .data_err_i                (data_err),

    .irq_software_i            ('0),
    .irq_timer_i               ('0),
    .irq_external_i            ('0),
    .irq_fast_i                (15'h0),
    .irq_nm_i                  (1'b0),

    .scramble_key_valid_i      (1'b0),
    .scramble_key_i            (128'h0),
    .scramble_nonce_i          (64'h0),
    .scramble_req_o            (),

    .debug_req_i               (1'b0),
    .crash_dump_o              (),
    .double_fault_seen_o       (),

    .fetch_enable_i            (ibex_pkg::IbexMuBiOn),
    .alert_minor_o             (),
    .alert_major_internal_o    (),
    .alert_major_bus_o         (),
    .core_sleep_o              (),

    .lockstep_cmp_en_o         (),

    .data_req_shadow_o         (),
    .data_we_shadow_o          (),
    .data_be_shadow_o          (),
    .data_addr_shadow_o        (),
    .data_wdata_shadow_o       (),
    .data_wdata_intg_shadow_o  (),

    .instr_req_shadow_o        (),
    .instr_addr_shadow_o       ()
  );

  // No instruction memory is needed as instructions are provided by TestRIG.
  // However, we do need to provide realistic flow-control.
  assign instr_gnt = instr_req;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      instr_rvalid <= 1'b0;
    end else begin
      instr_rvalid <= instr_req;
    end
  end

  // SRAM block for data memory.
  // Check the addresses fall within the range used by the sail model.
  assign data_gnt = data_req;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data_err <= 'b0;
    end else begin
      data_err <= !(('h8000_0000 <= data_addr) && (data_addr < 'h8080_0000));
    end
  end
  ram_1p #(
    .Depth (RamDepth) // depth in 32-bit words
  ) u_ram (
    .clk_i    (clk),
    .rst_ni   (rst_n),
    .req_i    (data_req),
    .we_i     (data_we),
    .be_i     (data_be),
    .addr_i   (data_addr),
    .wdata_i  (data_wdata),
    .rvalid_o (data_rvalid),
    .rdata_o  (data_rdata)
  );

  // Tag RAM: 1 bit per word, driven in parallel with u_ram.
  prim_ram_1p #(
    .Width           (1),
    .Depth           (RamDepth),
    .DataBitsPerMask (1)
  ) u_tag_ram (
    .clk_i     (clk),
    .rst_ni    (rst_n),
    .req_i     (data_req),
    .write_i   (data_we),
    .addr_i    (data_addr[RamAddrW+1:2]),
    .wdata_i   (data_tag_wr),
    .wmask_i   (1'b1),
    .rdata_o   (data_tag_rd),
    .cfg_i     (prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT),
    .cfg_o     ()
  );

  // RVFI interface connections
  assign rvfi_if.reset                = ~rst_n;
  assign rvfi_if.valid                = dut.rvfi_valid;
  assign rvfi_if.order                = dut.rvfi_order;
  assign rvfi_if.insn                 = dut.rvfi_insn;
  assign rvfi_if.trap                 = dut.rvfi_trap;
  assign rvfi_if.halt                 = dut.rvfi_halt;
  assign rvfi_if.intr                 = dut.rvfi_intr;
  assign rvfi_if.mode                 = dut.rvfi_mode;
  assign rvfi_if.ixl                  = dut.rvfi_ixl;
  assign rvfi_if.rs1_addr             = dut.rvfi_rs1_addr;
  assign rvfi_if.rs2_addr             = dut.rvfi_rs2_addr;
  assign rvfi_if.rs1_rdata            = dut.rvfi_rs1_rdata;
  assign rvfi_if.rs2_rdata            = dut.rvfi_rs2_rdata;
  assign rvfi_if.rd_addr              = dut.rvfi_rd_addr;
  assign rvfi_if.rd_wdata             = dut.rvfi_rd_wdata;
  assign rvfi_if.rs1_rcap             = cheriot_cap_to_mem(dut.rvfi_rs1_rcap);
  assign rvfi_if.rs2_rcap             = cheriot_cap_to_mem(dut.rvfi_rs2_rcap);
  assign rvfi_if.rd_wcap              = cheriot_cap_to_mem(dut.rvfi_rd_wcap);
  assign rvfi_if.pc_rdata             = dut.rvfi_pc_rdata;
  assign rvfi_if.pc_wdata             = dut.rvfi_pc_wdata;
  assign rvfi_if.mem_addr             = dut.rvfi_mem_addr;
  assign rvfi_if.mem_rmask            = dut.rvfi_mem_rmask;
  assign rvfi_if.mem_rdata            = dut.rvfi_mem_rdata;
  assign rvfi_if.mem_wdata            = dut.rvfi_mem_wdata;
  assign rvfi_if.mem_wmask            = dut.rvfi_mem_wmask;
  assign rvfi_if.mem_is_cap           = dut.rvfi_mem_is_cap;
  assign rvfi_if.mem_rcap             = cheriot_cap_to_mem(dut.rvfi_mem_rcap);
  assign rvfi_if.mem_wcap             = cheriot_cap_to_mem(dut.rvfi_mem_wcap);
  assign rvfi_if.ext_pre_mip          = dut.rvfi_ext_pre_mip;
  assign rvfi_if.ext_post_mip         = dut.rvfi_ext_post_mip;
  assign rvfi_if.ext_nmi              = dut.rvfi_ext_nmi;
  assign rvfi_if.ext_nmi_int          = dut.rvfi_ext_nmi_int;
  assign rvfi_if.ext_debug_req        = dut.rvfi_ext_debug_req;
  assign rvfi_if.ext_rf_wr_suppress   = dut.rvfi_ext_rf_wr_suppress;
  assign rvfi_if.ext_mcycle           = dut.rvfi_ext_mcycle;
  assign rvfi_if.ext_mhpmcounters     = dut.rvfi_ext_mhpmcounters;
  assign rvfi_if.ext_mhpmcountersh    = dut.rvfi_ext_mhpmcountersh;
  assign rvfi_if.ext_ic_scr_key_valid = dut.rvfi_ext_ic_scr_key_valid;
  assign rvfi_if.ext_irq_valid        = dut.rvfi_ext_irq_valid;

  `define IBEX_DII_INSN_PATH dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.dii_insn
  `define IBEX_DII_ACK_PATH dut.u_ibex_top.u_ibex_core.if_stage_i.gen_prefetch_buffer.prefetch_buffer_i.fifo_i.dii_ack

  assign `IBEX_DII_INSN_PATH = dii_if.dii_insn;
  assign dii_if.dii_ack = `IBEX_DII_ACK_PATH;

  `define IBEX_RF_FF_PATH dut.u_ibex_top.gen_regfile_ff.register_file_i
  `define IBEX_MEPC_PATH dut.u_ibex_top.u_ibex_core.cs_registers_i.u_mepc_csr.rdata_q
  `define IBEX_MSTATUS_PATH dut.u_ibex_top.u_ibex_core.cs_registers_i.u_mstatus_csr.rdata_q

  // Initialise register file capabilities to the root data capability
  // upon every reset to match cheriot-sail. This makes random testing easier.
  // TODO: do similar for shadow register file ECC values if start testing SecureIbex.
  for (genvar i = 1; i < 16; i++) begin : g_tb_rf_force_reset
    initial begin
      while (1) begin
        @(posedge rst_n);    // handle multiple-reset case
        force `IBEX_RF_FF_PATH.g_cheriot_rf.g_rf_shared_flops[i].rf_reg_q = cheriot_regcap_to_vec(ROOT_CAP_TM);
        @(posedge clk);
        release `IBEX_RF_FF_PATH.g_cheriot_rf.g_rf_shared_flops[i].rf_reg_q;
      end
    end
  end
  // Force some CSR bits to certain reset/constant to match cheriot-sail.
  // Specifically: pre-populate MEPC, invert MPIE reset, restrict to M-mode.
  initial begin
    while (1) begin
      @(posedge rst_n);    // handle multiple-reset case
      force `IBEX_MEPC_PATH = 32'h8000_0000;
      force `IBEX_MSTATUS_PATH[4] = 1'b0; // MPIE
      force `IBEX_MSTATUS_PATH[3:2] = 2'b11; // MPP
      @(posedge clk);
      release `IBEX_MEPC_PATH;
      release `IBEX_MSTATUS_PATH[4];
      // do NOT release mstatus MPP bits
    end
  end
  // Zero the testbench data and tag memories on reset to match cheriot-sail
  initial begin
    while (1) begin
      @(posedge rst_n);    // handle multiple-reset case
      for (integer i=0; i<RamDepth; i++) begin
        u_ram.u_ram.mem[i] = 32'b0;
        u_tag_ram.mem[i]   =  1'b0;
      end
      // prim_ram_1p's rdata_o is a plain flop only ever assigned on a read. Initialize it here to
      // avoid Xs in the simulation before the first read.
      u_ram.u_ram.rdata_o = 32'b0;
      u_tag_ram.rdata_o   =  1'b0;
    end
  end

  initial begin
    clk_if.set_active();

    fork
      clk_if.apply_reset(.reset_width_clks(10));
    join_none

    uvm_config_db#(virtual clk_rst_if)::set(null, "*", "clk_if", clk_if);
    uvm_config_db#(virtual core_ibex_dii_intf)::set(null, "*", "dii_if", dii_if);
    uvm_config_db#(virtual core_ibex_rvfi_if)::set(null, "*", "rvfi_if", rvfi_if);

    run_test();
  end
endmodule
