module aida_lca
  import ibex_pkg::*;
  import redmule_pkg::*;
  import isolde_tcdm_pkg::*;
  import aida_lca_package::*;
#(
    parameter bit          PMPEnable        = 1'b0,
    parameter int unsigned PMPGranularity   = 0,
    parameter int unsigned PMPNumRegions    = 4,
    parameter int unsigned MHPMCounterNum   = 0,
    parameter int unsigned MHPMCounterWidth = 40,
    parameter bit          RV32E            = 1'b0,
    parameter rv32m_e      RV32M            = RV32MFast,
    parameter rv32b_e      RV32B            = RV32BNone,
    parameter regfile_e    RegFile          = RegFileFF,
    parameter bit          BranchTargetALU  = 1'b0,
    parameter bit          WritebackStage   = 1'b0,
    parameter bit          ICache           = 1'b0,
    parameter bit          ICacheECC        = 1'b0,
    parameter bit          BranchPredictor  = 1'b0,
    parameter bit          DbgTriggerEn     = 1'b0,
    parameter int unsigned DbgHwBreakNum    = 1,
    parameter bit          SecureIbex       = 1'b0,
    parameter bit          ICacheScramble   = 1'b0,
    parameter lfsr_seed_t  RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
    parameter lfsr_perm_t  RndCnstLfsrPerm  = RndCnstLfsrPermDefault,
    parameter int unsigned DmHaltAddr       = 32'h1A110800,
    parameter int unsigned DmExceptionAddr  = 32'h1A110808
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,
    input  logic                  fetch_enable_i,
           isolde_tcdm_if.master  aida_data_memory,
           isolde_tcdm_if.master  aida_stack_memory,
           isolde_tcdm_if.master  aida_instr_memory,
           isolde_tcdm_if.master  aida_mmio,
    // ===  Scratchpad Memory (SPM) banks  connections ===
    output isolde_tcdm_pkg::req_t spm_req_o        [N_TCDM_BANKS-1:0],
    input  isolde_tcdm_pkg::rsp_t spm_rsp_i        [N_TCDM_BANKS-1:0],
    // === JTAG port ===
    input  jtag_pkg::jtag_req_t   aida_jtag_in,
    output jtag_pkg::jtag_rsp_t   aida_jtag_out

);

  logic [rv_dm_pkg::NrHarts-1:0]      debug_req;
  logic                               core_sleep;
  logic [                NC-1:0][1:0] evt;

  /********************************************************/
  /**          Router configurations                     **/
  /*******************************************************/

  // DATA
  typedef enum {

    PERIPH_IDX,
    DATA_IDX,
    STACK_IDX,
    MMIO_IDX,
    SPM_IDX,
`ifdef TARGET_RV_DEBUG
    DEBUG_IDX,
`endif
    LAST_IDX
  } data_map_idx_t;

  localparam int unsigned NoRules = LAST_IDX;
  // 
  localparam addr_range_t addr_map[NoRules] = '{
      '{start_addr: PERIPH_ADDR, end_addr: IMEM_ADDR},
      '{start_addr: DMEM_ADDR, end_addr: DMEM_ADDR + DMEM_SIZE},
      '{start_addr: SMEM_ADDR, end_addr: SMEM_ADDR + SMEM_SIZE},
      '{start_addr: MMIO_ADDR, end_addr: MMIO_ADDR_END},
      '{start_addr: SPM_NARROW_ADDR, end_addr: SPM_NARROW_ADDR + SPM_NARROW_SIZE}
      //`ifdef TARGET_RV_DEBUG
      , '{start_addr: DEBUG_ADDR, end_addr: DEBUG_ADDR + DEBUG_SIZE}
  //`endif
  };

`ifdef TARGET_RV_DEBUG
  // DEBUG MODULE PERIPHERAL, instructions memory map
  typedef enum {
    INSTR_MEM_IDX,
    INSTR_DEBUG_IDX,
    INSTR_LAST_IDX
  } instr_map_idx_t;

  localparam int unsigned InstrNoRules = INSTR_LAST_IDX;
  // 
  localparam addr_range_t instr_map[InstrNoRules] = '{
      '{start_addr: IMEM_ADDR, end_addr: IMEM_ADDR + IMEM_SIZE},
      '{start_addr: DEBUG_ADDR, end_addr: DEBUG_ADDR + DEBUG_SIZE}
  };
  // DEBUG MODULE SYSTEM_BUS_ACCESS (dm_sba) memory map
  typedef enum {
    DM_SBA_IMEM_IDX,  //instructions
    DM_SBA_DMEM_IDX,  //data
    DM_SBA_SMEM_IDX,  //stack
    DM_SBA_SPM_IDX,   // scratchpad memory
    DM_SBA_LAST_IDX
  } sba_map_idx_t;

  // 
  localparam addr_range_t dm_sba_map[DM_SBA_LAST_IDX] = '{
      '{start_addr: IMEM_ADDR, end_addr: IMEM_ADDR + IMEM_SIZE},
      '{start_addr: DMEM_ADDR, end_addr: DMEM_ADDR + DMEM_SIZE},
      '{start_addr: SMEM_ADDR, end_addr: SMEM_ADDR + SMEM_SIZE},
      '{start_addr: SPM_NARROW_ADDR, end_addr: SPM_NARROW_ADDR + SPM_NARROW_SIZE}
  };
`endif
  /********************************************************/
  /**           Interface Definitions                   **/
  /*******************************************************/

  // === hardware accelerator  interconnect ===
  hci_core_intf #(.DW(HCI_DW)) redmule_hci (.clk(clk_i));


  // === Data port ===
  isolde_tcdm_if tcdm_core_data ();
  isolde_tcdm_if tcdm_dmem_muxed ();
  isolde_tcdm_if redmule_ctrl ();  // HWE peripheral  interface

  // === stack memory port ===
  isolde_tcdm_if tcdm_stack_muxed ();

  // === instruction memory port ===
  isolde_tcdm_if tcdm_core_inst ();
  isolde_tcdm_if tcdm_imem_muxed ();

  // === debugger module ports ===
  isolde_tcdm_if tcdm_dm_periph ();
  isolde_tcdm_if tcdm_dm_sba ();

  // === Scratchpad memory(SPM) ports ===
  isolde_tcdm_if tcdm_spm_dma ();
  isolde_tcdm_if tcdm_spm_dma_muxed ();


  // === Data Network on Chip NoC interfaces ===
  isolde_tcdm_pkg::req_t noc_data_reqs[LAST_IDX];
  isolde_tcdm_pkg::rsp_t noc_data_rsps[LAST_IDX];
  // === Instruction Network on Chip NoC interfaces ===
  isolde_tcdm_pkg::req_t noc_instr_reqs[INSTR_LAST_IDX];
  isolde_tcdm_pkg::rsp_t noc_instr_rsps[INSTR_LAST_IDX];
  // === Debug module System Bus Access (dm_sba) Network on Chip NoC interfaces ===
  isolde_tcdm_pkg::req_t noc_dm_sba_reqs[DM_SBA_LAST_IDX];
  isolde_tcdm_pkg::rsp_t noc_dm_sba_rsps[DM_SBA_LAST_IDX];

  /********************************************************/
  /**           Router(s)                                **/
  /*******************************************************/

  isolde_router #(
      .N_RULES(NoRules),
      .ADDR_RANGES(addr_map)
  ) i_isolde_data_router (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(tcdm_core_data),
      .req_o       (noc_data_reqs),
      .rsp_i       (noc_data_rsps)
  );

  isolde_router #(
      .N_RULES(InstrNoRules),
      .ADDR_RANGES(instr_map)
  ) i_isolde_instr_router (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(tcdm_core_inst),
      .req_o       (noc_instr_reqs),
      .rsp_i       (noc_instr_rsps)
  );

  isolde_router #(
      .N_RULES(DM_SBA_LAST_IDX),
      .ADDR_RANGES(dm_sba_map)
  ) i_isolde_dm_sba_router (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(tcdm_dm_sba),
      .req_o       (noc_dm_sba_reqs),
      .rsp_i       (noc_dm_sba_rsps)
  );

  /********************************************************/
  /**           memory mapped I/O                        **/
  /*******************************************************/

  assign aida_mmio.req = noc_data_reqs[MMIO_IDX];
  assign noc_data_rsps[MMIO_IDX] = aida_mmio.rsp;


  /********************************************************/
  /**     RV Debug Module                                **/
  /*******************************************************/

  isolde_mux_tcdm i_mux_dm_periph (
      .clk_i,
      .rst_ni,
      .req_2_i(noc_data_reqs[DEBUG_IDX]),
      .req_1_i(noc_instr_reqs[INSTR_DEBUG_IDX]),
      .rsp_2_o(noc_data_rsps[DEBUG_IDX]),
      .rsp_1_o(noc_instr_rsps[INSTR_DEBUG_IDX]),
      .tcdm_master_o(tcdm_dm_periph)
  );

  isolde_mux_tcdm i_mux_dm_sb_imem (
      .clk_i,
      .rst_ni,
      .req_1_i(noc_dm_sba_reqs[DM_SBA_IMEM_IDX]),
      .req_2_i(noc_instr_reqs[INSTR_MEM_IDX]),
      .rsp_1_o(noc_dm_sba_rsps[DM_SBA_IMEM_IDX]),
      .rsp_2_o(noc_instr_rsps[INSTR_MEM_IDX]),
      .tcdm_master_o(tcdm_imem_muxed)
  );


  isolde_mux_tcdm i_mux_dm_sb_dmem (
      .clk_i,
      .rst_ni,
      .req_1_i(noc_dm_sba_reqs[DM_SBA_DMEM_IDX]),
      .req_2_i(noc_data_reqs[DATA_IDX]),
      .rsp_1_o(noc_dm_sba_rsps[DM_SBA_DMEM_IDX]),
      .rsp_2_o(noc_data_rsps[DATA_IDX]),
      .tcdm_master_o(tcdm_dmem_muxed)
  );

  isolde_mux_tcdm i_mux_dm_sb_stack (
      .clk_i,
      .rst_ni,
      .req_1_i(noc_dm_sba_reqs[DM_SBA_SMEM_IDX]),
      .req_2_i(noc_data_reqs[STACK_IDX]),
      .rsp_1_o(noc_dm_sba_rsps[DM_SBA_SMEM_IDX]),
      .rsp_2_o(noc_data_rsps[STACK_IDX]),
      .tcdm_master_o(tcdm_stack_muxed)
  );


  isolde_mux_tcdm i_mux_dm_sb_spm (
      .clk_i,
      .rst_ni,
      .req_1_i(noc_dm_sba_reqs[DM_SBA_SPM_IDX]),
      .req_2_i(noc_data_reqs[SPM_IDX]),
      .rsp_1_o(noc_dm_sba_rsps[DM_SBA_SPM_IDX]),
      .rsp_2_o(noc_data_rsps[SPM_IDX]),
      .tcdm_master_o(tcdm_spm_dma_muxed)
  );

  rv_dm #() i_rv_dm (
      .clk_i,
      .rst_ni,
      /// Debug Module Interface (DMI) slave port 
      .s_periph(tcdm_dm_periph),
      //.s_dmi(tcdm_inst_dm),
      /// System Bus master port
      .m_sba(tcdm_dm_sba),
      /// JTAG
      .jtag_in(aida_jtag_in),
      .jtag_out(aida_jtag_out),
      .debug_req_o(debug_req)
  );


  /********************************************************/
  /**     TCDM                                           **/
  /*******************************************************/


  isolde_addr_shim_wrp #(
      .START_ADDR(SPM_NARROW_ADDR),  // Set start address
      .END_ADDR(SPM_NARROW_ADDR + SPM_NARROW_SIZE)  // Set end address
  ) i_tcdm_spm_dma_shim (
      .tcdm_slave_i (tcdm_spm_dma_muxed),
      .tcdm_master_o(tcdm_spm_dma)
  );

  isolde_tcdm_interconnect #(
      .ALIGN (1'b0),
      .HCI_DW(HCI_DW)
  ) i_tcdm_interconnect (
      .clk_i,
      .rst_ni,
      .s_hci_core (redmule_hci),
      .s_tcdm_core(tcdm_spm_dma),
      .mem_req_o  (spm_req_o),
      .mem_rsp_i  (spm_rsp_i)
  );

  /********************************************************/
  /**     Data memory                                    **/
  /*******************************************************/

  isolde_addr_shim_wrp #(
      .START_ADDR(IMEM_ADDR),  // Set start address
      .END_ADDR(IMEM_ADDR + GMEM_SIZE)  // Set end address
  ) i_dmem_shim (
      .tcdm_slave_i (tcdm_dmem_muxed),
      .tcdm_master_o(aida_data_memory)
  );


  /********************************************************/
  /**     Instruction memory                             **/
  /*******************************************************/

  isolde_addr_shim_wrp #(
      .START_ADDR(IMEM_ADDR),  // Set start address
      .END_ADDR(IMEM_ADDR + GMEM_SIZE)  // Set end address
  ) i_imem_shim (
      .tcdm_slave_i (tcdm_imem_muxed),
      .tcdm_master_o(aida_instr_memory)
  );


  /********************************************************/
  /**     Stack memory                                   **/
  /*******************************************************/

  isolde_addr_shim_wrp #(
      .START_ADDR(SMEM_ADDR),  // Set start address
      .END_ADDR(SMEM_ADDR + SMEM_SIZE)  // Set end address
  ) i_stack_mem_shim (
      .tcdm_slave_i (tcdm_stack_muxed),
      .tcdm_master_o(aida_stack_memory)
  );


  /********************************************************/
  /**     CV-X-IF                                        **/
  /*******************************************************/

  isolde_cv_x_if #(
      .X_NUM_RS   (isolde_cv_x_if_pkg::X_NUM_RS),
      .X_ID_WIDTH (isolde_cv_x_if_pkg::X_ID_WIDTH),
      .X_MEM_WIDTH(isolde_cv_x_if_pkg::X_MEM_WIDTH),
      .X_RFR_WIDTH(isolde_cv_x_if_pkg::X_RFR_WIDTH),
      .X_RFW_WIDTH(isolde_cv_x_if_pkg::X_RFW_WIDTH),
      .X_MISA     (isolde_cv_x_if_pkg::X_MISA),
      .X_ECS_XS   (isolde_cv_x_if_pkg::X_ECS_XS)
  ) itf_core_xif ();

  xif_monitor_cpu_issue xif_monitor_cpu_issue_i (
      clk_i,
      itf_core_xif
  );

  /********************************************************/
  /**     IBEX core                                     **/
  /*******************************************************/

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
  ) i_ibex_tracing (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .test_en_i  (1'b0),
      .scan_rst_ni(1'b1),
      .ram_cfg_i  (prim_ram_1p_pkg::RAM_1P_CFG_DEFAULT),

      .hart_id_i        (32'b0),
      // First instruction executed is at 0x0 + 0x80
      .boot_addr_i      (BOOT_ADDR),
      // === Instruction memory interface
      .instr_req_o      (tcdm_core_inst.req.req),
      .instr_gnt_i      (tcdm_core_inst.rsp.gnt),
      .instr_rvalid_i   (tcdm_core_inst.rsp.valid),
      .instr_addr_o     (tcdm_core_inst.req.addr),
      .instr_rdata_i    (tcdm_core_inst.rsp.data),
      //.instr_rdata_intg_i     (instr_rdata_intg),
      //.instr_err_i            (instr_err),
      // === Data memory interface
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
      .xif_compressed_if     (itf_core_xif.cpu_compressed),
      .xif_issue_if          (itf_core_xif.cpu_issue),
      .xif_commit_if         (itf_core_xif.cpu_commit),
      .xif_mem_if            (itf_core_xif.cpu_mem),
      .xif_mem_result_if     (itf_core_xif.cpu_mem_result),
      .xif_result_if         (itf_core_xif.cpu_result)
  );

  /********************************************************/
  /**     Hardware Engine HWE                            **/
  /*******************************************************/

  assign redmule_ctrl.req = noc_data_reqs[PERIPH_IDX];
  assign noc_data_rsps[PERIPH_IDX] = redmule_ctrl.rsp;

  isolde_redmule_top #(
      .ID_WIDTH (ID),
      .N_CORES  (NC),
      .DW       (HCI_DW),  // TCDM port dimension (in bits
      .AddrWidth(HCI_AW)
  ) i_redmule_top (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .test_mode_i   (REDMULE_TEST_MODE),
      .fetch_enable_i(fetch_enable_i),
      .evt_o         (evt),
      .m_hci_core    (redmule_hci),
      .s_tcdm_ctrl   (redmule_ctrl)
  );
  isolde_hci_monitor #(
      .AW  (HCI_AW),
      .DW  (HCI_DW),
      .NAME("spm_hci_monitor")
  ) i_hci_monitor (
      .clk_i,
      .rst_ni,
      .hci_core(redmule_hci)
  );

endmodule
