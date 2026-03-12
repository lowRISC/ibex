// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Ibex lockstep module
// This module instantiates a second copy of the core logic, and compares it's outputs against
// those from the main core. The second core runs synchronously with the main core, delayed by
// LockstepOffset cycles.
// SEC_CM: LOGIC.SHADOW
module ibex_lockstep import ibex_pkg::*; import cheri_pkg::*; #(
  parameter int unsigned            LockstepOffset              = 1,
  parameter bit                     PMPEnable                   = 1'b0,
  parameter int unsigned            PMPGranularity              = 0,
  parameter int unsigned            PMPNumRegions               = 4,
  parameter ibex_pkg::pmp_cfg_t     PMPRstCfg[PMP_MAX_REGIONS]  = ibex_pkg::PmpCfgRst,
  parameter logic [PMP_ADDR_MSB:0]  PMPRstAddr[PMP_MAX_REGIONS] = ibex_pkg::PmpAddrRst,
  parameter ibex_pkg::pmp_mseccfg_t PMPRstMsecCfg               = ibex_pkg::PmpMseccfgRst,
  parameter int unsigned            MHPMCounterNum              = 0,
  parameter int unsigned            MHPMCounterWidth            = 40,
  parameter bit                     RV32E                       = 1'b0,
  parameter rv32m_e                 RV32M                       = RV32MFast,
  parameter rv32b_e                 RV32B                       = RV32BNone,
  parameter rv32zc_e                RV32ZC                      = RV32ZcaZcbZcmp,
  parameter bit                     BranchTargetALU             = 1'b0,
  parameter bit                     WritebackStage              = 1'b0,
  parameter bit                     ICache                      = 1'b0,
  parameter bit                     ICacheECC                   = 1'b0,
  parameter bit                     ICacheTweakInfection        = 1'b0,
  parameter int unsigned            BusSizeECC                  = BUS_SIZE,
  parameter int unsigned            TagSizeECC                  = IC_TAG_SIZE,
  parameter int unsigned            LineSizeECC                 = IC_LINE_SIZE,
  parameter bit                     BranchPredictor             = 1'b0,
  parameter bit                     DbgTriggerEn                = 1'b0,
  parameter int unsigned            DbgHwBreakNum               = 1,
  parameter bit                     ResetAll                    = 1'b0,
  parameter lfsr_seed_t             RndCnstLfsrSeed             = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t             RndCnstLfsrPerm             = RndCnstLfsrPermDefault,
  parameter bit                     SecureIbex                  = 1'b0,
  parameter bit                     DummyInstructions           = 1'b0,
  parameter bit                     RegFileECC                  = 1'b0,
  parameter int unsigned            RegFileDataWidth            = 32,
  parameter int unsigned            RegFileDataEccWidth         = 39,
  parameter regfile_e               RegFile                     = RegFileFF,
  parameter bit                     MemECC                      = 1'b0,
  parameter int unsigned            MemDataWidth                = MemECC ? 32 + 7 : 32,
  parameter int unsigned            DmBaseAddr                  = 32'h1A110000,
  parameter int unsigned            DmAddrMask                  = 32'h00000FFF,
  parameter int unsigned            DmHaltAddr                  = 32'h1A110800,
  parameter int unsigned            DmExceptionAddr             = 32'h1A110808,
  // mvendorid: encoding of manufacturer/provider
  parameter logic [31:0]            CsrMvendorId                = 32'b0,
  // marchid: encoding of base microarchitecture
  parameter logic [31:0]            CsrMimpId                   = 32'b0,
  // CHERIoT parameters
  parameter bit                     CHERIoTEn                   = 1'b1,
  parameter int unsigned            DataWidth                   = 33,
  parameter int unsigned            HeapBase                    = 32'h2001_0000,
  parameter int unsigned            TSMapBase                   = 32'h2002_f000,
  parameter int unsigned            TSMapSize                   = 1024,
  parameter bit                     MemCapFmt                   = 1'b0,
  parameter bit                     CheriPPLBC                  = 1'b1,
  parameter bit                     CheriSBND2                  = 1'b0,
  parameter bit                     CheriTBRE                   = 1'b1,
  parameter int unsigned            MMRegDinW                   = 128,
  parameter int unsigned            MMRegDoutW                  = 64
) (
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,
  input  logic                         cheri_pmode_i,
  input  logic                         cheri_tsafe_en_i,

  input  logic                         instr_req_i,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  input  logic [31:0]                  instr_addr_i,
  input  logic [MemDataWidth-1:0]      instr_rdata_i,
  input  logic                         instr_err_i,

  input  logic                         data_req_i,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  input  logic                         data_we_i,
  input  logic [3:0]                   data_be_i,
  input  logic [31:0]                  data_addr_i,
  input  logic [DataWidth-1:0]         data_wdata_i,
  input  logic                         data_is_cap_i,
  output logic [6:0]                   data_wdata_intg_o,
  input  logic [MemDataWidth-1:0]      data_rdata_i,
  input  logic [6:0]                   data_rdata_intg_i,
  input  logic                         data_err_i,

  input  logic                         dummy_instr_id_i,
  input  logic [4:0]                   rf_raddr_a_i,
  input  logic [4:0]                   rf_raddr_b_i,
  input  logic [4:0]                   rf_waddr_wb_i,
  input  logic                         rf_we_wb_i,
  input  logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_a_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_b_i,

  input  reg_cap_t                     rf_wcap_wb_i,
  input  reg_cap_t                     rf_rcap_a_i,
  input  reg_cap_t                     rf_rcap_b_i,
  input  logic [31:0]                  rf_reg_rdy_i,
  input  logic                         rf_trsv_en_i,
  input  logic [4:0]                   rf_trsv_addr_i,
  input  logic [6:0]                   rf_trsv_par_i,
  input  logic [4:0]                   rf_trvk_addr_i,
  input  logic                         rf_trvk_en_i,
  input  logic                         rf_trvk_clrtag_i,
  input  logic [6:0]                   rf_trvk_par_i,
  input  logic                         tsmap_cs_i,
  input  logic [15:0]                  tsmap_addr_i,
  input  logic [31:0]                  tsmap_rdata_i,
  input  logic [6:0]                   tsmap_rdata_intg_i,
  input  logic [MMRegDinW-1:0]         mmreg_corein_i,
  input  logic [MMRegDoutW-1:0]        mmreg_coreout_i,
  input  logic [IC_NUM_WAYS-1:0]       ic_tag_req_i,
  input  logic                         ic_tag_write_i,
  input  logic [IC_INDEX_W-1:0]        ic_tag_addr_i,
  input  logic [TagSizeECC-1:0]        ic_tag_wdata_i,
  input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
  input  logic [IC_NUM_WAYS-1:0]       ic_data_req_i,
  input  logic                         ic_data_write_i,
  input  logic [IC_INDEX_W-1:0]        ic_data_addr_i,
  input  logic [LineSizeECC-1:0]       ic_data_wdata_i,
  input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],
  input  logic                         ic_scr_key_valid_i,
  input  logic                         ic_scr_key_req_i,

  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,
  input  logic                         irq_pending_i,

  input  logic                         debug_req_i,
  input  crash_dump_t                  crash_dump_i,
  input  logic                         double_fault_seen_i,

  input  ibex_mubi_t                   fetch_enable_i,
  input  ibex_mubi_t                   mcounteren_writable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  input  ibex_mubi_t                   core_busy_i,
  input  logic                         test_en_i,
  input  logic                         scan_rst_ni,

  output ibex_mubi_t                   lockstep_cmp_en_o,
  output logic                         data_req_shadow_o,
  output logic                         data_we_shadow_o,
  output logic [3:0]                   data_be_shadow_o,
  output logic [31:0]                  data_addr_shadow_o,
  output logic [31:0]                  data_wdata_shadow_o,
  output logic [6:0]                   data_wdata_intg_shadow_o,
  output logic                         instr_req_shadow_o,
  output logic [31:0]                  instr_addr_shadow_o
);

  import prim_secded_pkg::SecdedInv3932ZeroWord;

  localparam int unsigned LockstepOffsetW = prim_util_pkg::vbits(LockstepOffset);
  // Core outputs are delayed for an extra cycle due to shadow output registers
  localparam int unsigned OutputsOffset = LockstepOffset + 1;

  //////////////////////
  // Reset generation //
  //////////////////////
  logic                       rst_shadow_cnt_err;
  ibex_mubi_t                 rst_shadow_set_d, rst_shadow_set_q;
  logic                       rst_shadow_n;
  ibex_mubi_t                 enable_cmp_d, enable_cmp_q;
  if (LockstepOffset > 1) begin : gen_reset_counter
    // Upon reset, the comparison is stopped and the shadow core is reset, both immediately. A
    // counter is started. After LockstepOffset clock cycles:
    // - The counter is stopped.
    // - The reset of the shadow core is synchronously released.
    // The comparison is started in the following clock cycle.

    logic [LockstepOffsetW-1:0] rst_shadow_cnt;
    // This counter primitive starts counting to LockstepOffset after a system
    // reset. The counter value saturates at LockstepOffset.
    prim_count #(
      .Width      (LockstepOffsetW        ),
      .ResetValue (LockstepOffsetW'(1'b0) )
    ) u_rst_shadow_cnt (
      .clk_i              (clk_i                  ),
      .rst_ni             (rst_ni                 ),
      .clr_i              (1'b0                   ),
      .set_i              (1'b0                   ),
      .set_cnt_i          ('0                     ),
      .incr_en_i          (1'b1                   ),
      .decr_en_i          (1'b0                   ),
      .step_i             (LockstepOffsetW'(1'b1) ),
      .commit_i           (1'b1                   ),
      .cnt_o              (rst_shadow_cnt         ),
      .cnt_after_commit_o (                       ),
      .err_o              (rst_shadow_cnt_err     )
    );

    // When the LockstepOffset counter value is reached, activate the lockstep
    // comparison.
    assign rst_shadow_set_d =
      (rst_shadow_cnt >= LockstepOffsetW'(LockstepOffset - 1)) ? IbexMuBiOn : IbexMuBiOff;

    // Enable lockstep comparison.
    assign enable_cmp_d = rst_shadow_set_q;

  end else begin : gen_no_reset_counter
    // Assert rst_shadow_set_d as soon as we have the first clk_i and rst_ni posedge.
    // The reset of the shadow core will then be enabled with a delay of 1 cycle with
    // rst_shadow_set_q.
    assign rst_shadow_set_d = IbexMuBiOn;

    // Tie off this error as it is not used in the `LockstepOffset = 1` case.
    assign rst_shadow_cnt_err = 1'b0;

    // Delay the comparison enable signal by 1 cycle.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        enable_cmp_d <= IbexMuBiOff;
      end else begin
        enable_cmp_d <= IbexMuBiOn;
      end
    end

    // Tie off the upper unused bits of rst_shadow_set_q.
    logic [2:0] unused_bits;
    assign unused_bits = rst_shadow_set_q[3:1];
  end

  // The primitives below are used to place size-only constraints in order to prevent
  // synthesis optimizations and preserve anchor points for constraining backend tools.
  prim_flop #(
    .Width(IbexMuBiWidth),
    .ResetValue(IbexMuBiOff)
  ) u_prim_rst_shadow_set_flop (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .d_i   (rst_shadow_set_d),
    .q_o   (rst_shadow_set_q)
  );

  prim_flop #(
    .Width(IbexMuBiWidth),
    .ResetValue(IbexMuBiOff)
  ) u_prim_enable_cmp_flop (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .d_i   (enable_cmp_d),
    .q_o   (enable_cmp_q)
  );

  prim_clock_mux2 #(
    .NoFpgaBufG(1'b1)
  ) u_prim_rst_shadow_n_mux2 (
    .clk0_i(rst_shadow_set_q[0]),
    .clk1_i(scan_rst_ni),
    .sel_i (test_en_i),
    .clk_o (rst_shadow_n)
  );

  //////////////////
  // Input delays //
  //////////////////

  typedef struct packed {
    logic                        instr_gnt;
    logic                        instr_rvalid;
    logic [MemDataWidth-1:0]     instr_rdata;
    logic                        instr_err;
    logic                        data_gnt;
    logic                        data_rvalid;
    logic [DataWidth-1:0]        data_rdata;
    logic                        data_err;
    logic [RegFileDataWidth-1:0] rf_rdata_a;
    logic [RegFileDataWidth-1:0] rf_rdata_b;
    logic                        irq_software;
    logic                        irq_timer;
    logic                        irq_external;
    logic [14:0]                 irq_fast;
    logic                        irq_nm;
    logic                        debug_req;
    ibex_mubi_t                  fetch_enable;
    ibex_mubi_t                  mcounteren_writable;
    logic                        ic_scr_key_valid;
    logic                        cheri_pmode;
    logic                        cheri_tsafe_en;
    reg_cap_t                    rf_rcap_a;
    reg_cap_t                    rf_rcap_b;
    logic [31:0]                 rf_reg_rdy;
    logic [31:0]                 tsmap_rdata;
    logic [MMRegDinW-1:0]        mmreg_corein;
  } delayed_inputs_t;

  delayed_inputs_t [LockstepOffset-1:0] shadow_inputs_q;
  delayed_inputs_t                      shadow_inputs_in;
  logic [6:0]                           instr_rdata_intg_q, data_rdata_intg_q;
  logic [6:0]                           tsmap_rdata_intg_q;
  // Packed arrays must be dealt with separately
  logic [TagSizeECC-1:0]                shadow_tag_rdata_delayed [IC_NUM_WAYS];
  logic [LineSizeECC-1:0]               shadow_data_rdata_delayed [IC_NUM_WAYS];
  if (LockstepOffset > 1) begin : gen_multi_cycle_delay
    logic [TagSizeECC-1:0]  shadow_tag_rdata_q [IC_NUM_WAYS][LockstepOffset];
    logic [LineSizeECC-1:0] shadow_data_rdata_q [IC_NUM_WAYS][LockstepOffset];

    assign shadow_tag_rdata_delayed = shadow_tag_rdata_q[0];
    assign shadow_data_rdata_delayed = shadow_data_rdata_q[0];

    // Delay the ic_tag_rdata_i and ic_data_rdata_i inputs by LockstepOffset cycles.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        for (int unsigned i = 0; i < LockstepOffset; i++) begin
          shadow_inputs_q[i]     <= delayed_inputs_t'('0);
          shadow_tag_rdata_q[i]  <= '{default: 0};
          shadow_data_rdata_q[i] <= '{default: 0};
        end
      end else begin
        for (int unsigned i = 0; i < LockstepOffset - 1; i++) begin
          shadow_inputs_q[i]     <= shadow_inputs_q[i+1];
          shadow_tag_rdata_q[i]  <= shadow_tag_rdata_q[i+1];
          shadow_data_rdata_q[i] <= shadow_data_rdata_q[i+1];
        end
        shadow_inputs_q[LockstepOffset-1]     <= shadow_inputs_in;
        shadow_tag_rdata_q[LockstepOffset-1]  <= ic_tag_rdata_i;
        shadow_data_rdata_q[LockstepOffset-1] <= ic_data_rdata_i;
      end
    end
  end else begin : gen_single_cycle_delay
    // If LockstepOffset = 1, using:
    // logic [TagSizeECC-1:0]                shadow_tag_rdata_q [IC_NUM_WAYS][LockstepOffset];
    // logic [TagSizeECC-1:0]                shadow_tag_rdata_q [IC_NUM_WAYS][LockstepOffset];
    // aborts the compilation with an error message:
    // `port or terminal connection type check failed on instance`
    // Hence, in this case, remove the unpacked array dimension.
    logic [TagSizeECC-1:0]                shadow_tag_rdata_q [IC_NUM_WAYS];
    logic [LineSizeECC-1:0]               shadow_data_rdata_q [IC_NUM_WAYS];

    assign shadow_tag_rdata_delayed = shadow_tag_rdata_q;
    assign shadow_data_rdata_delayed = shadow_data_rdata_q;

    // Delay the ic_tag_rdata_i and ic_data_rdata_i inputs by 1 cycle.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        shadow_inputs_q     <= delayed_inputs_t'('0);
        shadow_tag_rdata_q  <= '{default: 0};
        shadow_data_rdata_q <= '{default: 0};
      end else begin
        shadow_inputs_q     <= shadow_inputs_in;
        shadow_tag_rdata_q  <= ic_tag_rdata_i;
        shadow_data_rdata_q <= ic_data_rdata_i;
      end
    end
  end

  // Assign the inputs to the delay structure
  assign shadow_inputs_in.instr_gnt           = instr_gnt_i;
  assign shadow_inputs_in.instr_rvalid        = instr_rvalid_i;
  assign shadow_inputs_in.instr_rdata         = instr_rdata_i;
  assign shadow_inputs_in.instr_err           = instr_err_i;
  assign shadow_inputs_in.data_gnt            = data_gnt_i;
  assign shadow_inputs_in.data_rvalid         = data_rvalid_i;
  assign shadow_inputs_in.data_rdata          = data_rdata_i;
  assign shadow_inputs_in.data_err            = data_err_i;
  assign shadow_inputs_in.rf_rdata_a          = rf_rdata_a_i;
  assign shadow_inputs_in.rf_rdata_b          = rf_rdata_b_i;
  assign shadow_inputs_in.irq_software        = irq_software_i;
  assign shadow_inputs_in.irq_timer           = irq_timer_i;
  assign shadow_inputs_in.irq_external        = irq_external_i;
  assign shadow_inputs_in.irq_fast            = irq_fast_i;
  assign shadow_inputs_in.irq_nm              = irq_nm_i;
  assign shadow_inputs_in.debug_req           = debug_req_i;
  assign shadow_inputs_in.fetch_enable        = fetch_enable_i;
  assign shadow_inputs_in.mcounteren_writable = mcounteren_writable_i;
  assign shadow_inputs_in.ic_scr_key_valid    = ic_scr_key_valid_i;
  assign shadow_inputs_in.cheri_pmode         = cheri_pmode_i;
  assign shadow_inputs_in.cheri_tsafe_en      = cheri_tsafe_en_i;
  assign shadow_inputs_in.rf_rcap_a           = rf_rcap_a_i;
  assign shadow_inputs_in.rf_rcap_b           = rf_rcap_b_i;
  assign shadow_inputs_in.rf_reg_rdy          = rf_reg_rdy_i;
  assign shadow_inputs_in.tsmap_rdata         = tsmap_rdata_i;
  assign shadow_inputs_in.mmreg_corein        = mmreg_corein_i;

  // Delay the inputs
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_rdata_intg_q <= '0;
      data_rdata_intg_q  <= '0;
      tsmap_rdata_intg_q  <= '0;
      for (int unsigned i = 0; i < LockstepOffset; i++) begin
        shadow_inputs_q[i]     <= delayed_inputs_t'('0);
        shadow_tag_rdata_q[i]  <= '{default: 0};
        shadow_data_rdata_q[i] <= '{default: 0};
      end
    end else begin
      instr_rdata_intg_q <= instr_rdata_intg_i;
      data_rdata_intg_q  <= data_rdata_intg_i;
      tsmap_rdata_intg_q  <= tsmap_rdata_intg_i;
      for (int unsigned i = 0; i < LockstepOffset - 1; i++) begin
        shadow_inputs_q[i]     <= shadow_inputs_q[i+1];
        shadow_tag_rdata_q[i]  <= shadow_tag_rdata_q[i+1];
        shadow_data_rdata_q[i] <= shadow_data_rdata_q[i+1];
      end
      shadow_inputs_q[LockstepOffset-1]     <= shadow_inputs_in;
      shadow_tag_rdata_q[LockstepOffset-1]  <= ic_tag_rdata_i;
      shadow_data_rdata_q[LockstepOffset-1] <= ic_data_rdata_i;
    end
  end

  ////////////////////////////
  // Bus integrity checking //
  ////////////////////////////

  logic        bus_intg_err;
  logic [1:0]  instr_intg_err, data_intg_err, data_intg_err_tmp;
  logic [31:0] unused_wdata;
  logic [1:0]  data_we_q;
  logic [31:0] rdata_tmp;

  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      data_we_q <= 2'b00;
    end else begin
      if (data_gnt_i) data_we_q[1] <= data_we_i;
      data_we_q[0] <= data_we_q[1];    // align with shadow_inputs_q[LockstepOffset-1]
    end
  end

  // Checks on incoming data
  prim_secded_inv_39_32_dec u_instr_intg_dec (
    .data_i     ({instr_rdata_intg_q, shadow_inputs_q[LockstepOffset-1].instr_rdata}),
    .data_o     (),
    .syndrome_o (),
    .err_o      (instr_intg_err)
  );

  if (CHERIoTEn) begin
    assign rdata_tmp = shadow_inputs_q[LockstepOffset-1].data_rdata[31:0] ^
                       {31'h0, shadow_inputs_q[LockstepOffset-1].data_rdata[32]};
  end else begin
    assign rdata_tmp = shadow_inputs_q[LockstepOffset-1].data_rdata[31:0];
  end

  prim_secded_inv_39_32_dec u_data_intg_dec (
    .data_i     ({data_rdata_intg_q, rdata_tmp}),
    .data_o     (),
    .syndrome_o (),
    .err_o      (data_intg_err_tmp)
  );

  // only check read data (data_rvalid includes both reads and writes)
  assign data_intg_err = data_we_q[0] ? 2'h0 : data_intg_err_tmp;

  assign bus_intg_err = (shadow_inputs_q[LockstepOffset-1].instr_rvalid & |instr_intg_err) |
                        (shadow_inputs_q[LockstepOffset-1].data_rvalid  & |data_intg_err);

  // Generate integrity bits
  if (CHERIoTEn) begin
    prim_secded_inv_39_32_enc u_data_gen (
      .data_i (data_wdata_i[31:0]^{31'h0, data_wdata_i[32]}),
      .data_o ({data_wdata_intg_o, unused_wdata})
    );
  end else begin
    prim_secded_inv_39_32_enc u_data_gen (
      .data_i (data_wdata_i[31:0]),
      .data_o ({data_wdata_intg_o, unused_wdata})
    );
  end


  ////////////////////////////////////////
  // TSMAP interface integrity checking //
  ////////////////////////////////////////

  logic       tsmap_intg_err;
  logic [1:0] tsmap_intg_err_tmp;
  logic [1:0] tsmap_cs_q;

  if (CHERIoTEn && CheriPPLBC) begin
    always @(posedge clk_i, negedge rst_ni) begin
      if (~rst_ni) begin
        tsmap_cs_q <= 2'b00;
      end else begin
        tsmap_cs_q <= {tsmap_cs_i, tsmap_cs_q[1]}; // align with shadow_inputs_q[LockstepOffset-1]
      end
    end

    // Checks on incoming data
    prim_secded_inv_39_32_dec u_tsmap_intg_dec (
      .data_i     ({tsmap_rdata_intg_q, shadow_inputs_q[LockstepOffset-1].tsmap_rdata}),
      .data_o     (),
      .syndrome_o (),
      .err_o      (tsmap_intg_err_tmp)
    );

    assign tsmap_intg_err = tsmap_cs_q[0] & tsmap_intg_err_tmp;

  end else begin
    assign tsmap_intg_err = 1'b0;
  end
  ///////////////////
  // Output delays //
  ///////////////////

  typedef struct packed {
    logic                    instr_req;
    logic [31:0]             instr_addr;
    logic                    data_req;
    logic                    data_we;
    logic [3:0]              data_be;
    logic [31:0]             data_addr;
    logic [DataWidth-1:0]    data_wdata;
    logic                    data_is_cap;
    logic                    dummy_instr_id;
    logic [4:0]              rf_raddr_a;
    logic [4:0]              rf_raddr_b;
    logic [4:0]              rf_waddr_wb;
    logic                    rf_we_wb;
    logic [RegFileDataWidth-1:0] rf_wdata_wb_ecc;
    logic [IC_NUM_WAYS-1:0]  ic_tag_req;
    logic                    ic_tag_write;
    logic [IC_INDEX_W-1:0]   ic_tag_addr;
    logic [TagSizeECC-1:0]   ic_tag_wdata;
    logic [IC_NUM_WAYS-1:0]  ic_data_req;
    logic                    ic_data_write;
    logic [IC_INDEX_W-1:0]   ic_data_addr;
    logic [LineSizeECC-1:0]  ic_data_wdata;
    logic                    ic_scr_key_req;
    logic                    irq_pending;
    crash_dump_t             crash_dump;
    logic                    double_fault_seen;
    ibex_mubi_t              core_busy;
    logic                    icache_inval;
    reg_cap_t                rf_wcap_wb;
    logic                    rf_trsv_en;
    logic [4:0]              rf_trsv_addr;
    logic [6:0]              rf_trsv_par;
    logic [4:0]              rf_trvk_addr;
    logic                    rf_trvk_en;
    logic                    rf_trvk_clrtag;
    logic [6:0]              rf_trvk_par;
    logic                    tsmap_cs;
    logic [15:0]             tsmap_addr;
    logic [MMRegDoutW-1:0]   mmreg_coreout;
  } delayed_outputs_t;

  delayed_outputs_t [OutputsOffset-1:0]  core_outputs_q;
  delayed_outputs_t                      core_outputs_in;
  delayed_outputs_t                      shadow_outputs_d, shadow_outputs_q;

  // Assign core outputs to the structure
  assign core_outputs_in.instr_req           = instr_req_i;
  assign core_outputs_in.instr_addr          = instr_addr_i;
  assign core_outputs_in.data_req            = data_req_i;
  assign core_outputs_in.data_we             = data_we_i;
  assign core_outputs_in.data_be             = data_be_i;
  assign core_outputs_in.data_addr           = data_addr_i;
  assign core_outputs_in.data_wdata          = data_wdata_i;
  assign core_outputs_in.data_is_cap         = data_is_cap_i;
  assign core_outputs_in.dummy_instr_id      = dummy_instr_id_i;
  assign core_outputs_in.rf_raddr_a          = rf_raddr_a_i;
  assign core_outputs_in.rf_raddr_b          = rf_raddr_b_i;
  assign core_outputs_in.rf_waddr_wb         = rf_waddr_wb_i;
  assign core_outputs_in.rf_we_wb            = rf_we_wb_i;
  assign core_outputs_in.rf_wdata_wb_ecc     = rf_wdata_wb_ecc_i;
  assign core_outputs_in.ic_tag_req          = ic_tag_req_i;
  assign core_outputs_in.ic_tag_write        = ic_tag_write_i;
  assign core_outputs_in.ic_tag_addr         = ic_tag_addr_i;
  assign core_outputs_in.ic_tag_wdata        = ic_tag_wdata_i;
  assign core_outputs_in.ic_data_req         = ic_data_req_i;
  assign core_outputs_in.ic_data_write       = ic_data_write_i;
  assign core_outputs_in.ic_data_addr        = ic_data_addr_i;
  assign core_outputs_in.ic_data_wdata       = ic_data_wdata_i;
  assign core_outputs_in.ic_scr_key_req      = ic_scr_key_req_i;
  assign core_outputs_in.irq_pending         = irq_pending_i;
  assign core_outputs_in.crash_dump          = crash_dump_i;
  assign core_outputs_in.double_fault_seen   = double_fault_seen_i;
  assign core_outputs_in.core_busy           = core_busy_i;
  assign core_outputs_in.rf_wcap_wb          = rf_wcap_wb_i;
  assign core_outputs_in.rf_trsv_en          = rf_trsv_en_i;
  assign core_outputs_in.rf_trsv_addr        = rf_trsv_addr_i;
  assign core_outputs_in.rf_trsv_par         = rf_trsv_par_i;
  assign core_outputs_in.rf_trvk_addr        = rf_trvk_addr_i;
  assign core_outputs_in.rf_trvk_en          = rf_trvk_en_i;
  assign core_outputs_in.rf_trvk_clrtag      = rf_trvk_clrtag_i;
  assign core_outputs_in.rf_trvk_par         = rf_trvk_par_i;
  assign core_outputs_in.tsmap_cs            = tsmap_cs_i;
  assign core_outputs_in.tsmap_addr          = tsmap_addr_i;
  assign core_outputs_in.mmreg_coreout       = mmreg_coreout_i;

  // Delay the outputs
  always_ff @(posedge clk_i) begin
    for (int unsigned i = 0; i < OutputsOffset - 1; i++) begin
      core_outputs_q[i] <= core_outputs_q[i+1];
    end
    core_outputs_q[OutputsOffset-1] <= core_outputs_in;
  end

  // The following outputs are generated by the shadow core and directly fed into the shadow core
  // register file. There is no need to compare those signals against the signals generated by the
  // main core in the lockstep comparison. A fault into one of those signals will cause a mismatch
  // in the main core and shadow core register file instances. As the outputs of both register
  // files are combined, the ECC checker inside the shadow core will detect the fault.
  logic [RegFileDataEccWidth-1:0] shadow_rf_wdata_wb_ecc;
  logic [4:0]                     shadow_rf_raddr_a;
  logic [4:0]                     shadow_rf_raddr_b;
  logic [4:0]                     shadow_rf_waddr_wb;
  logic                           shadow_rf_we_wb;
  logic                           shadow_dummy_instr_id;
  logic                           shadow_dummy_instr_wb;

  // The following output does not need to be checked in the lockstep comparison as we anyways
  // check the data_wdata itself.
  logic [6:0]                     shadow_data_wdata_intg;

  ///////////////////////////////
  // Shadow core instantiation //
  ///////////////////////////////

  logic shadow_alert_minor, shadow_alert_major_internal, shadow_alert_major_bus;
  logic [RegFileDataEccWidth - RegFileDataWidth - 1:0] shadow_rf_rdata_a_intg;
  logic [RegFileDataEccWidth - RegFileDataWidth - 1:0] shadow_rf_rdata_b_intg;

  ibex_core #(
    .PMPEnable            ( PMPEnable            ),
    .PMPGranularity       ( PMPGranularity       ),
    .PMPNumRegions        ( PMPNumRegions        ),
    .PMPRstCfg            ( PMPRstCfg            ),
    .PMPRstAddr           ( PMPRstAddr           ),
    .PMPRstMsecCfg        ( PMPRstMsecCfg        ),
    .MHPMCounterNum       ( MHPMCounterNum       ),
    .MHPMCounterWidth     ( MHPMCounterWidth     ),
    .RV32E                ( RV32E                ),
    .RV32M                ( RV32M                ),
    .RV32B                ( RV32B                ),
    .RV32ZC               ( RV32ZC               ),
    .BranchTargetALU      ( BranchTargetALU      ),
    .ICache               ( ICache               ),
    .ICacheECC            ( ICacheECC            ),
    .ICacheTweakInfection ( ICacheTweakInfection ),
    .BusSizeECC           ( BusSizeECC           ),
    .TagSizeECC           ( TagSizeECC           ),
    .LineSizeECC          ( LineSizeECC          ),
    .BranchPredictor      ( BranchPredictor      ),
    .DbgTriggerEn         ( DbgTriggerEn         ),
    .DbgHwBreakNum        ( DbgHwBreakNum        ),
    .WritebackStage       ( WritebackStage       ),
    .ResetAll             ( ResetAll             ),
    .RndCnstLfsrSeed      ( RndCnstLfsrSeed      ),
    .RndCnstLfsrPerm      ( RndCnstLfsrPerm      ),
    .SecureIbex           ( SecureIbex           ),
    .DummyInstructions    ( DummyInstructions    ),
    .RegFileECC           ( RegFileECC           ),
    .RegFileDataWidth     ( RegFileDataEccWidth  ),
    .MemECC               ( MemECC               ),
    .MemDataWidth         ( MemDataWidth         ),
    .DmBaseAddr           ( DmBaseAddr           ),
    .DmAddrMask           ( DmAddrMask           ),
    .DmHaltAddr           ( DmHaltAddr           ),
    .DmExceptionAddr      ( DmExceptionAddr      ),
    .CsrMvendorId         ( CsrMvendorId         ),
    .CsrMimpId            ( CsrMimpId            ),
    .CHERIoTEn            ( CHERIoTEn            ),
    .DataWidth            ( DataWidth            ),
    .HeapBase             ( HeapBase             ),
    .TSMapBase            ( TSMapBase            ),
    .TSMapSize            ( TSMapSize            ),
    .MemCapFmt            ( MemCapFmt            ),
    .CheriPPLBC           ( CheriPPLBC           ),
    .CheriSBND2           ( CheriSBND2           ),
    .CheriTBRE            ( CheriTBRE            )
  ) u_shadow_core (
    .clk_i               (clk_i),
    .rst_ni              (rst_shadow_n),

    .hart_id_i           (hart_id_i),
    .boot_addr_i         (boot_addr_i),

    .cheri_pmode_i       (shadow_inputs_q[0].cheri_pmode),
    .cheri_tsafe_en_i    (shadow_inputs_q[0].cheri_tsafe_en),

    .instr_req_o         (shadow_outputs_d.instr_req),
    .instr_gnt_i         (shadow_inputs_q[0].instr_gnt),
    .instr_rvalid_i      (shadow_inputs_q[0].instr_rvalid),
    .instr_addr_o        (shadow_outputs_d.instr_addr),
    .instr_rdata_i       (shadow_inputs_q[0].instr_rdata),
    .instr_err_i         (shadow_inputs_q[0].instr_err),

    .data_req_o          (shadow_outputs_d.data_req),
    .data_gnt_i          (shadow_inputs_q[0].data_gnt),
    .data_rvalid_i       (shadow_inputs_q[0].data_rvalid),
    .data_we_o           (shadow_outputs_d.data_we),
    .data_be_o           (shadow_outputs_d.data_be),
    .data_addr_o         (shadow_outputs_d.data_addr),
    .data_wdata_o        (shadow_outputs_d.data_wdata),
    .data_is_cap_o       (shadow_outputs_d.data_is_cap),
    .data_rdata_i        (shadow_inputs_q[0].data_rdata),
    .data_err_i          (shadow_inputs_q[0].data_err),

    .dummy_instr_id_o    (shadow_outputs_d.dummy_instr_id),
    .rf_raddr_a_o        (shadow_outputs_d.rf_raddr_a),
    .rf_raddr_b_o        (shadow_outputs_d.rf_raddr_b),
    .rf_waddr_wb_o       (shadow_outputs_d.rf_waddr_wb),
    .rf_we_wb_o          (shadow_outputs_d.rf_we_wb),
    .rf_wdata_wb_ecc_o   (shadow_outputs_d.rf_wdata_wb_ecc),
    .rf_rdata_a_ecc_i    ({shadow_rf_rdata_a_intg, shadow_inputs_q[0].rf_rdata_a}),
    .rf_rdata_b_ecc_i    ({shadow_rf_rdata_b_intg, shadow_inputs_q[0].rf_rdata_b}),
    .rf_wcap_wb_o        (shadow_outputs_d.rf_wcap_wb),
    .rf_rcap_a_i         (shadow_inputs_q[0].rf_rcap_a),
    .rf_rcap_b_i         (shadow_inputs_q[0].rf_rcap_b),
    .rf_reg_rdy_i        (shadow_inputs_q[0].rf_reg_rdy),
    .rf_trsv_en_o        (shadow_outputs_d.rf_trsv_en),
    .rf_trsv_addr_o      (shadow_outputs_d.rf_trsv_addr),
    .rf_trsv_par_o       (shadow_outputs_d.rf_trsv_par),
    .rf_trvk_addr_o      (shadow_outputs_d.rf_trvk_addr),
    .rf_trvk_en_o        (shadow_outputs_d.rf_trvk_en),
    .rf_trvk_clrtag_o    (shadow_outputs_d.rf_trvk_clrtag),
    .rf_trvk_par_o       (shadow_outputs_d.rf_trvk_par),
    .tsmap_cs_o          (shadow_outputs_d.tsmap_cs),
    .tsmap_addr_o        (shadow_outputs_d.tsmap_addr),
    .tsmap_rdata_i       (shadow_inputs_q[0].tsmap_rdata),
    .mmreg_corein_i      (shadow_inputs_q[0].tsmap_rdata),
    .mmreg_coreout_o     (shadow_outputs_d.mmreg_coreout),

    .ic_tag_req_o        (shadow_outputs_d.ic_tag_req),
    .ic_tag_write_o      (shadow_outputs_d.ic_tag_write),
    .ic_tag_addr_o       (shadow_outputs_d.ic_tag_addr),
    .ic_tag_wdata_o      (shadow_outputs_d.ic_tag_wdata),
    .ic_tag_rdata_i      (shadow_tag_rdata_delayed),
    .ic_data_req_o       (shadow_outputs_d.ic_data_req),
    .ic_data_write_o     (shadow_outputs_d.ic_data_write),
    .ic_data_addr_o      (shadow_outputs_d.ic_data_addr),
    .ic_data_wdata_o     (shadow_outputs_d.ic_data_wdata),
    .ic_data_rdata_i     (shadow_data_rdata_delayed),
    .ic_scr_key_valid_i  (shadow_inputs_q[0].ic_scr_key_valid),
    .ic_scr_key_req_o    (shadow_outputs_d.ic_scr_key_req),

    .irq_software_i      (shadow_inputs_q[0].irq_software),
    .irq_timer_i         (shadow_inputs_q[0].irq_timer),
    .irq_external_i      (shadow_inputs_q[0].irq_external),
    .irq_fast_i          (shadow_inputs_q[0].irq_fast),
    .irq_nm_i            (shadow_inputs_q[0].irq_nm),
    .irq_pending_o       (shadow_outputs_d.irq_pending),

    .debug_req_i         (shadow_inputs_q[0].debug_req),
    .crash_dump_o        (shadow_outputs_d.crash_dump),
    .double_fault_seen_o (shadow_outputs_d.double_fault_seen),

`ifdef RVFI
    .rvfi_valid                   (),
    .rvfi_order                   (),
    .rvfi_insn                    (),
    .rvfi_trap                    (),
    .rvfi_halt                    (),
    .rvfi_intr                    (),
    .rvfi_mode                    (),
    .rvfi_ixl                     (),
    .rvfi_rs1_addr                (),
    .rvfi_rs2_addr                (),
    .rvfi_rs3_addr                (),
    .rvfi_rs1_rdata               (),
    .rvfi_rs2_rdata               (),
    .rvfi_rs3_rdata               (),
    .rvfi_rd_addr                 (),
    .rvfi_rd_wdata                (),
    .rvfi_pc_rdata                (),
    .rvfi_pc_wdata                (),
    .rvfi_mem_addr                (),
    .rvfi_mem_rmask               (),
    .rvfi_mem_wmask               (),
    .rvfi_mem_rdata               (),
    .rvfi_mem_wdata               (),
    .rvfi_ext_pre_mip             (),
    .rvfi_ext_post_mip            (),
    .rvfi_ext_nmi                 (),
    .rvfi_ext_nmi_int             (),
    .rvfi_ext_debug_req           (),
    .rvfi_ext_debug_mode          (),
    .rvfi_ext_rf_wr_suppress      (),
    .rvfi_ext_mcycle              (),
    .rvfi_ext_mhpmcounters        (),
    .rvfi_ext_mhpmcountersh       (),
    .rvfi_ext_ic_scr_key_valid    (),
    .rvfi_ext_irq_valid           (),
    .rvfi_ext_expanded_insn_valid (),
    .rvfi_ext_expanded_insn       (),
    .rvfi_ext_expanded_insn_last  (),
    .rvfi_mem_wcap                (),
    .rvfi_mem_rcap                (),
    .rvfi_mem_is_cap              (),
    .rvfi_rd_wcap                 (),
    .rvfi_rs2_rcap                (),
    .rvfi_rs1_rcap                (),
`endif

    .fetch_enable_i         (shadow_inputs_q[0].fetch_enable),
    .mcounteren_writable_i  (shadow_inputs_q[0].mcounteren_writable),
    .alert_minor_o          (shadow_alert_minor),
    .alert_major_internal_o (shadow_alert_major_internal),
    .alert_major_bus_o      (shadow_alert_major_bus),
    .core_busy_o            (shadow_outputs_d.core_busy)
  );

  // Register the shadow core outputs
  always_ff @(posedge clk_i) begin
    shadow_outputs_q <= shadow_outputs_d;
  end

  // The lower RegFileDataWidth bits (which are the data bits) are not fed into the shadow
  // register file as they are handled by the main register file.
  logic [RegFileDataWidth-1:0] unused_shadow_rf_wdata_wb_ecc;
  assign unused_shadow_rf_wdata_wb_ecc = shadow_rf_wdata_wb_ecc[RegFileDataWidth-1:0];

  //////////////////////////
  // Shadow register file //
  //////////////////////////
  // SEC_CM: DATA_REG_SW.GLITCH_DETECT
  if (RegFile == RegFileFF) begin : gen_shadow_regfile_ff
    ibex_register_file_ff #(
      .RV32E            (RV32E),
      .DataWidth        (RegFileDataEccWidth - RegFileDataWidth),
      .DummyInstructions(DummyInstructions),
      .WordZeroVal      (SecdedInv3932ZeroWord[RegFileDataEccWidth-1:RegFileDataWidth])
    ) register_file_shadow_i (
      .clk_i            (clk_i),
      .rst_ni           (rst_shadow_n),

      .test_en_i        (test_en_i),
      .dummy_instr_id_i (shadow_dummy_instr_id),
      .dummy_instr_wb_i (shadow_dummy_instr_wb),

      .raddr_a_i        (shadow_rf_raddr_a),
      .rdata_a_o        (shadow_rf_rdata_a_intg),
      .raddr_b_i        (shadow_rf_raddr_b),
      .rdata_b_o        (shadow_rf_rdata_b_intg),
      .waddr_a_i        (shadow_rf_waddr_wb),
      .wdata_a_i        (shadow_rf_wdata_wb_ecc[RegFileDataEccWidth-1:RegFileDataWidth]),
      .we_a_i           (shadow_rf_we_wb)
    );
  end else if (RegFile == RegFileFPGA) begin : gen_regfile_fpga
    ibex_register_file_fpga #(
      .RV32E            (RV32E),
      .DataWidth        (RegFileDataEccWidth - RegFileDataWidth),
      .DummyInstructions(DummyInstructions),
      .WordZeroVal      (SecdedInv3932ZeroWord[RegFileDataEccWidth-1:RegFileDataWidth])
    ) register_file_shadow_i (
      .clk_i            (clk_i),
      .rst_ni           (rst_shadow_n),

      .test_en_i        (test_en_i),
      .dummy_instr_id_i (shadow_dummy_instr_id),
      .dummy_instr_wb_i (shadow_dummy_instr_wb),

      .raddr_a_i        (shadow_rf_raddr_a),
      .rdata_a_o        (shadow_rf_rdata_a_intg),
      .raddr_b_i        (shadow_rf_raddr_b),
      .rdata_b_o        (shadow_rf_rdata_b_intg),
      .waddr_a_i        (shadow_rf_waddr_wb),
      .wdata_a_i        (shadow_rf_wdata_wb_ecc[RegFileDataEccWidth-1:RegFileDataWidth]),
      .we_a_i           (shadow_rf_we_wb)
    );
  end else if (RegFile == RegFileLatch) begin : gen_regfile_latch
    ibex_register_file_latch #(
      .RV32E            (RV32E),
      .DataWidth        (RegFileDataEccWidth - RegFileDataWidth),
      .DummyInstructions(DummyInstructions),
      .WordZeroVal      (SecdedInv3932ZeroWord[RegFileDataEccWidth-1:RegFileDataWidth])
    ) register_file_shadow_i (
      .clk_i            (clk_i),
      .rst_ni           (rst_shadow_n),

      .test_en_i        (test_en_i),
      .dummy_instr_id_i (shadow_dummy_instr_id),
      .dummy_instr_wb_i (shadow_dummy_instr_wb),

      .raddr_a_i        (shadow_rf_raddr_a),
      .rdata_a_o        (shadow_rf_rdata_a_intg),
      .raddr_b_i        (shadow_rf_raddr_b),
      .rdata_b_o        (shadow_rf_rdata_b_intg),
      .waddr_a_i        (shadow_rf_waddr_wb),
      .wdata_a_i        (shadow_rf_wdata_wb_ecc[RegFileDataEccWidth-1:RegFileDataWidth]),
      .we_a_i           (shadow_rf_we_wb)
    );
  end

  /////////////////////////
  // Compare the outputs //
  /////////////////////////

  logic outputs_mismatch;

  // Any value except IbexMuBiOff will turn on the lockstep output comparison.
  assign outputs_mismatch =
    (enable_cmp_q != IbexMuBiOff) & (shadow_outputs_q != core_outputs_q[0]);

  assign alert_major_internal_o
    = outputs_mismatch | shadow_alert_major_internal | rst_shadow_cnt_err;
  assign alert_major_bus_o      = shadow_alert_major_bus | bus_intg_err | tsmap_intg_err;
  assign alert_minor_o          = shadow_alert_minor;

  assign lockstep_cmp_en_o = enable_cmp_q;

  assign data_req_shadow_o = shadow_outputs_d.data_req;
  assign data_we_shadow_o = shadow_outputs_d.data_we;
  assign data_be_shadow_o = shadow_outputs_d.data_be;
  assign data_addr_shadow_o = shadow_outputs_d.data_addr;
  assign data_wdata_shadow_o = shadow_outputs_d.data_wdata;
  assign data_wdata_intg_shadow_o = shadow_data_wdata_intg;
  assign instr_req_shadow_o = shadow_outputs_d.instr_req;
  assign instr_addr_shadow_o = shadow_outputs_d.instr_addr;
endmodule
