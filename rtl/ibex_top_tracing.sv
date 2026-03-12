// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Top level module of the ibex RISC-V core with tracing enabled
 */

module ibex_top_tracing import ibex_pkg::*; import cheri_pkg::*; #(
  parameter base_isa_e   BaseIsa              = BaseIsaRV32I,
  parameter bit          PMPEnable            = 1'b0,
  parameter int unsigned PMPGranularity       = 0,
  parameter int unsigned PMPNumRegions        = 4,
  parameter int unsigned MHPMCounterNum       = 0,
  parameter int unsigned MHPMCounterWidth     = 40,
  parameter bit          RV32E                = 1'b0,
  parameter rv32m_e      RV32M                = RV32MFast,
  parameter rv32b_e      RV32B                = RV32BNone,
  parameter rv32zc_e     RV32ZC               = RV32ZcaZcbZcmp,
  parameter regfile_e    RegFile              = RegFileFF,
  parameter bit          BranchTargetALU      = 1'b0,
  parameter bit          WritebackStage       = 1'b0,
  parameter bit          ICache               = 1'b0,
  parameter bit          ICacheECC            = 1'b0,
  parameter bit          ICacheTweakInfection = 1'b0,
  parameter bit          BranchPredictor      = 1'b0,
  parameter bit          DbgTriggerEn         = 1'b0,
  parameter int unsigned DbgHwBreakNum        = 1,
  parameter bit          SecureIbex           = 1'b0,
  parameter int unsigned LockstepOffset       = 1,
  parameter bit          MemECC               = SecureIbex,
  parameter int unsigned MemDataWidth         = MemECC ? 32 + 7 : 32,
  parameter bit          ICacheScramble       = 1'b0,
  parameter lfsr_seed_t  RndCnstLfsrSeed      = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t  RndCnstLfsrPerm      = RndCnstLfsrPermDefault,
  parameter int unsigned DmBaseAddr           = 32'h1A110000,
  parameter int unsigned DmAddrMask           = 32'h00000FFF,
  parameter int unsigned DmHaltAddr           = 32'h1A110800,
  parameter int unsigned DmExceptionAddr      = 32'h1A110808,
  parameter bit          CHERIoTEn            = 1'b1,
  parameter int unsigned DataWidth            = 33,
  parameter int unsigned HeapBase             = 32'h2001_0000,
  parameter int unsigned TSMapBase            = 32'h2004_0000, // 4kB default
  parameter int unsigned TSMapSize            = 1024,
  parameter bit          MemCapFmt            = 1'b0,
  parameter bit          CheriPPLBC           = 1'b1,
  parameter bit          CheriSBND2           = 1'b0,
  parameter bit          CheriTBRE            = 1'b1,
  parameter bit          CheriStkZ            = 1'b1,
  parameter bit          CheriCapIT8          = 1'b0,
  parameter int unsigned MMRegDinW            = 128,
  parameter int unsigned MMRegDoutW           = 64
) (
  // Clock and Reset
  input  logic                                                         clk_i,
  input  logic                                                         rst_ni,

  // enable all clock gates for testing
  input  logic                                                         test_en_i,
  input  logic                                                         scan_rst_ni,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [ibex_pkg::IC_NUM_WAYS-1:0] ram_cfg_icache_tag_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ibex_pkg::IC_NUM_WAYS-1:0] ram_cfg_icache_tag_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [ibex_pkg::IC_NUM_WAYS-1:0] ram_cfg_icache_data_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ibex_pkg::IC_NUM_WAYS-1:0] ram_cfg_icache_data_o,

  input  logic [31:0]                                                  trvk_heap_base_addr_i,

  input  logic                                                         cheri_pmode_i,
  input  logic                                                         cheri_tsafe_en_i,

  input  logic [31:0]                                                  hart_id_i,
  input  logic [31:0]                                                  boot_addr_i,

  // Instruction memory interface
  output logic                                                         instr_req_o,
  input  logic                                                         instr_gnt_i,
  input  logic                                                         instr_rvalid_i,
  output logic [31:0]                                                  instr_addr_o,
  input  logic [31:0]                                                  instr_rdata_i,
  input  logic [6:0]                                                   instr_rdata_intg_i,
  input  logic                                                         instr_err_i,

  // Data memory interface
  output logic                                                         data_req_o,
  output logic                                                         data_is_cap_o,
  input  logic                                                         data_gnt_i,
  input  logic                                                         data_rvalid_i,
  output logic                                                         data_we_o,
  output logic [3:0]                                                   data_be_o,
  output logic [31:0]                                                  data_addr_o,
  output logic [DataWidth-1:0]                                         data_wdata_o,
  output logic [6:0]                                                   data_wdata_intg_o,
  output logic                                                         data_tag_o,
  input  logic [DataWidth:0]                                           data_rdata_i,
  input  logic [6:0]                                                   data_rdata_intg_i,
  input  logic                                                         data_tag_i,
  input  logic                                                         data_err_i,

  // TRVK revocation bitmap read interface
  output logic                                                         trvk_revbm_req_o,
  input  logic                                                         trvk_revbm_gnt_i,
  input  logic                                                         trvk_revbm_rvalid_i,
  output logic [31:0]                                                  trvk_revbm_addr_o,
  input  logic [31:0]                                                  trvk_revbm_rdata_i,
  input  logic [6:0]                                                   trvk_revbm_rdata_intg_i,
  input  logic                                                         trvk_revbm_err_i,

  // TS map memory interface
  output logic                                                         tsmap_cs_o,
  output logic [15:0]                                                  tsmap_addr_o,
  input  logic [31:0]                                                  tsmap_rdata_i,
  input  logic [6:0]                                                   tsmap_rdata_intg_i,
  input  logic [MMRegDinW-1:0]                                         mmreg_corein_i,
  output logic [MMRegDoutW-1:0]                                        mmreg_coreout_o,

  // Interrupt inputs
  input  logic                                                         irq_software_i,
  input  logic                                                         irq_timer_i,
  input  logic                                                         irq_external_i,
  input  logic [14:0]                                                  irq_fast_i,
  // non-maskable interrupt
  input  logic                                                         irq_nm_i,

  // Scrambling Interface
  input  logic                                                         scramble_key_valid_i,
  input  logic [SCRAMBLE_KEY_W-1:0]                                    scramble_key_i,
  input  logic [SCRAMBLE_NONCE_W-1:0]                                  scramble_nonce_i,
  output logic                                                         scramble_req_o,

  // Debug Interface
  input  logic                                                         debug_req_i,
  output crash_dump_t                                                  crash_dump_o,
  output logic                                                         double_fault_seen_o,

  // CPU Control Signals
  input  ibex_mubi_t                                                   fetch_enable_i,
  input  ibex_mubi_t                                                   mcounteren_writable_i,
  output logic                                                         alert_minor_o,
  output logic                                                         alert_major_internal_o,
  output logic                                                         alert_major_bus_o,
  output logic                                                         core_sleep_o,

  // Lockstep signals
  output ibex_mubi_t                                                  lockstep_cmp_en_o,

  // Shadow core data interface outputs
  output logic                                                        data_req_shadow_o,
  output logic                                                        data_we_shadow_o,
  output logic [3:0]                                                  data_be_shadow_o,
  output logic [31:0]                                                 data_addr_shadow_o,
  output logic [31:0]                                                 data_wdata_shadow_o,
  output logic [6:0]                                                  data_wdata_intg_shadow_o,

  // Shadow core instruction interface outputs
  output logic                                                        instr_req_shadow_o,
  output logic [31:0]                                                 instr_addr_shadow_o
);

  // ibex_tracer relies on the signals from the RISC-V Formal Interface
  `ifndef RVFI
    $fatal("Fatal error: RVFI needs to be defined globally.");
  `endif

  logic        rvfi_valid;
  logic [63:0] rvfi_order;
  logic [31:0] rvfi_insn;
  logic        rvfi_trap;
  logic        rvfi_halt;
  logic        rvfi_intr;
  logic [ 1:0] rvfi_mode;
  logic [ 1:0] rvfi_ixl;
  logic [ 4:0] rvfi_rs1_addr;
  logic [ 4:0] rvfi_rs2_addr;
  logic [ 4:0] rvfi_rs3_addr;
  logic [31:0] rvfi_rs1_rdata;
  reg_cap_t    rvfi_rs1_rcap;
  reg_cap_t    rvfi_rs2_rcap;
  logic [31:0] rvfi_rs2_rdata;
  logic [31:0] rvfi_rs3_rdata;
  logic [ 4:0] rvfi_rd_addr;
  logic [31:0] rvfi_rd_wdata;
  reg_cap_t    rvfi_rd_wcap;
  logic [31:0] rvfi_pc_rdata;
  logic [31:0] rvfi_pc_wdata;
  logic [31:0] rvfi_mem_addr;
  logic [ 3:0] rvfi_mem_rmask;
  logic [ 3:0] rvfi_mem_wmask;
  logic [31:0] rvfi_mem_rdata;
  logic [31:0] rvfi_mem_wdata;
  logic        rvfi_mem_is_cap;
  reg_cap_t    rvfi_mem_rcap;
  reg_cap_t    rvfi_mem_wcap;
  logic [31:0] rvfi_mem2_addr;
  logic        rvfi_mem2_we;
  logic [65:0] rvfi_mem2_rdata;
  logic [65:0] rvfi_mem2_wdata;
  logic [31:0] rvfi_ext_pre_mip;
  logic [31:0] rvfi_ext_post_mip;
  logic        rvfi_ext_nmi;
  logic        rvfi_ext_nmi_int;
  logic        rvfi_ext_debug_req;
  logic        rvfi_ext_debug_mode;
  logic        rvfi_ext_rf_wr_suppress;
  logic [63:0] rvfi_ext_mcycle;

  logic [31:0] rvfi_ext_mhpmcounters [10];
  logic [31:0] rvfi_ext_mhpmcountersh [10];
  logic        rvfi_ext_ic_scr_key_valid;
  logic        rvfi_ext_irq_valid;
  logic        rvfi_ext_expanded_insn_valid;
  logic [15:0] rvfi_ext_expanded_insn;
  logic        rvfi_ext_expanded_insn_last;

  logic [31:0] unused_perf_regs [10];
  logic [31:0] unused_perf_regsh [10];


  logic [31:0] unused_rvfi_ext_pre_mip;
  logic [31:0] unused_rvfi_ext_post_mip;
  logic        unused_rvfi_ext_nmi;
  logic        unused_rvfi_ext_nmi_int;
  logic        unused_rvfi_ext_debug_req;
  logic        unused_rvfi_ext_debug_mode;
  logic        unused_rvfi_ext_rf_wr_suppress;
  logic [63:0] unused_rvfi_ext_mcycle;
  logic        unused_rvfi_ext_ic_scr_key_valid;
  logic        unused_rvfi_ext_irq_valid;
  logic        unused_rvfi_ext_expanded_insn_last;


  // Tracer doesn't use these signals, though other modules may probe down into tracer to observe
  // them.
  assign unused_rvfi_ext_pre_mip = rvfi_ext_pre_mip;
  assign unused_rvfi_ext_post_mip = rvfi_ext_post_mip;
  assign unused_rvfi_ext_nmi = rvfi_ext_nmi;
  assign unused_rvfi_ext_nmi_int = rvfi_ext_nmi_int;
  assign unused_rvfi_ext_debug_req = rvfi_ext_debug_req;
  assign unused_rvfi_ext_debug_mode = rvfi_ext_debug_mode;
  assign unused_rvfi_ext_rf_wr_suppress = rvfi_ext_rf_wr_suppress;
  assign unused_rvfi_ext_mcycle = rvfi_ext_mcycle;
  assign unused_perf_regs = rvfi_ext_mhpmcounters;
  assign unused_perf_regsh = rvfi_ext_mhpmcountersh;
  assign unused_rvfi_ext_ic_scr_key_valid = rvfi_ext_ic_scr_key_valid;
  assign unused_rvfi_ext_irq_valid = rvfi_ext_irq_valid;
  assign unused_rvfi_ext_expanded_insn_last = rvfi_ext_expanded_insn_last;

  ibex_top #(
    .BaseIsa              ( BaseIsa              ),
    .PMPEnable            ( PMPEnable            ),
    .PMPGranularity       ( PMPGranularity       ),
    .PMPNumRegions        ( PMPNumRegions        ),
    .MHPMCounterNum       ( MHPMCounterNum       ),
    .MHPMCounterWidth     ( MHPMCounterWidth     ),
    .RV32E                ( RV32E                ),
    .RV32M                ( RV32M                ),
    .RV32B                ( RV32B                ),
    .RV32ZC               ( RV32ZC               ),
    .RegFile              ( RegFile              ),
    .BranchTargetALU      ( BranchTargetALU      ),
    .ICache               ( ICache               ),
    .ICacheECC            ( ICacheECC            ),
    .ICacheTweakInfection ( ICacheTweakInfection ),
    .BranchPredictor      ( BranchPredictor      ),
    .DbgTriggerEn         ( DbgTriggerEn         ),
    .DbgHwBreakNum        ( DbgHwBreakNum        ),
    .WritebackStage       ( WritebackStage       ),
    .SecureIbex           ( SecureIbex           ),
    .LockstepOffset       ( LockstepOffset       ),
    .MemECC               ( MemECC               ),
    .MemDataWidth         ( MemDataWidth         ),
    .ICacheScramble       ( ICacheScramble       ),
    .RndCnstLfsrSeed      ( RndCnstLfsrSeed      ),
    .RndCnstLfsrPerm      ( RndCnstLfsrPerm      ),
    .DmBaseAddr           ( DmBaseAddr           ),
    .DmAddrMask           ( DmAddrMask           ),
    .DmHaltAddr           ( DmHaltAddr           ),
    .DmExceptionAddr      ( DmExceptionAddr      ),
    .CHERIoTEn            ( CHERIoTEn            ),
    .DataWidth            ( DataWidth            ),
    .HeapBase             ( HeapBase             ),
    .TSMapBase            ( TSMapBase            ),
    .TSMapSize            ( TSMapSize            ),
    .MemCapFmt            ( MemCapFmt            ),
    .CheriPPLBC           ( CheriPPLBC           ),
    .CheriSBND2           ( CheriSBND2           ),
    .CheriTBRE            ( CheriTBRE            ),
    .CheriStkZ            ( CheriStkZ            ),
    .CheriCapIT8          ( CheriCapIT8          )
  ) u_ibex_top (
    .clk_i,
    .rst_ni,

    .test_en_i,
    .scan_rst_ni,
    .ram_cfg_icache_tag_i,
    .ram_cfg_icache_tag_o,
    .ram_cfg_icache_data_i,
    .ram_cfg_icache_data_o,

    .cheri_pmode_i,
    .cheri_tsafe_en_i,
    .hart_id_i,
    .boot_addr_i,

    .instr_req_o,
    .instr_gnt_i,
    .instr_rvalid_i,
    .instr_addr_o,
    .instr_rdata_i,
    .instr_rdata_intg_i,
    .instr_err_i,

    .data_req_o,
    .data_is_cap_o,
    .data_gnt_i,
    .data_rvalid_i,
    .data_we_o,
    .data_be_o,
    .data_addr_o,
    .data_wdata_o,
    .data_wdata_intg_o,
    .data_rdata_i,
    .data_rdata_intg_i,
    .data_err_i,

    .trvk_heap_base_addr_i,
    .data_tag_o,
    .data_tag_i,
    .trvk_revbm_req_o,
    .trvk_revbm_gnt_i,
    .trvk_revbm_rvalid_i,
    .trvk_revbm_addr_o,
    .trvk_revbm_rdata_i,
    .trvk_revbm_rdata_intg_i,
    .trvk_revbm_err_i,

    .tsmap_cs_o,
    .tsmap_addr_o,
    .tsmap_rdata_i,
    .tsmap_rdata_intg_i,
    .mmreg_corein_i,
    .mmreg_coreout_o,

    .irq_software_i,
    .irq_timer_i,
    .irq_external_i,
    .irq_fast_i,
    .irq_nm_i,

    .scramble_key_valid_i,
    .scramble_key_i,
    .scramble_nonce_i,
    .scramble_req_o,

    .debug_req_i,
    .crash_dump_o,
    .double_fault_seen_o,

`ifdef RVFI
    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_ixl,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs3_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs1_rcap,
    .rvfi_rs2_rdata,
    .rvfi_rs2_rcap,
    .rvfi_rs3_rdata,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_rd_wcap,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata,
    .rvfi_mem_rcap,
    .rvfi_mem_wcap,
    .rvfi_mem_is_cap,
    .rvfi_ext_pre_mip,
    .rvfi_ext_post_mip,
    .rvfi_ext_nmi,
    .rvfi_ext_nmi_int,
    .rvfi_ext_debug_req,
    .rvfi_ext_debug_mode,
    .rvfi_ext_rf_wr_suppress,
    .rvfi_ext_mcycle,
    .rvfi_ext_mhpmcounters,
    .rvfi_ext_mhpmcountersh,
    .rvfi_ext_ic_scr_key_valid,
    .rvfi_ext_irq_valid,
    .rvfi_ext_expanded_insn_valid,
    .rvfi_ext_expanded_insn,
    .rvfi_ext_expanded_insn_last,
`endif

    .fetch_enable_i,
    .mcounteren_writable_i,
    .alert_minor_o,
    .alert_major_internal_o,
    .alert_major_bus_o,
    .core_sleep_o,

    .lockstep_cmp_en_o,

    .data_req_shadow_o,
    .data_we_shadow_o,
    .data_be_shadow_o,
    .data_addr_shadow_o,
    .data_wdata_shadow_o,
    .data_wdata_intg_shadow_o,

    .instr_req_shadow_o,
    .instr_addr_shadow_o
  );

`ifdef RVFI
  ibex_tracer #(
    .CheriCapIT8      (CheriCapIT8)
  ) u_ibex_tracer (
    .clk_i,
    .rst_ni,

    .cheri_pmode_i,
    .cheri_tsafe_en_i,
    .hart_id_i,

    .rvfi_valid,
    .rvfi_order,
    .rvfi_insn,
    .rvfi_trap,
    .rvfi_halt,
    .rvfi_intr,
    .rvfi_mode,
    .rvfi_ixl,
    .rvfi_rs1_addr,
    .rvfi_rs2_addr,
    .rvfi_rs3_addr,
    .rvfi_rs1_rdata,
    .rvfi_rs2_rdata,
    .rvfi_rs3_rdata,
    .rvfi_rs1_rcap,
    .rvfi_rs2_rcap,
    .rvfi_rd_wcap,
    .rvfi_rd_addr,
    .rvfi_rd_wdata,
    .rvfi_pc_rdata,
    .rvfi_pc_wdata,
    .rvfi_mem_addr,
    .rvfi_mem_rmask,
    .rvfi_mem_wmask,
    .rvfi_mem_rdata,
    .rvfi_mem_wdata,
    .rvfi_mem_rcap,
    .rvfi_mem_wcap,
    .rvfi_mem_is_cap,
    .rvfi_ext_expanded_insn_valid,
    .rvfi_ext_expanded_insn
  );
`endif

endmodule
