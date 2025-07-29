// Copyleft 2024 ISOLDE

`include "MemStatisticsCallback.svh"


timeunit 1ps; timeprecision 1ps;



class MyCallback extends MemStatisticsCallback;

  int unsigned m_instrMemLatency;

  function new(int unsigned instrMemLatency);
    super.new();
    m_instrMemLatency = instrMemLatency;
  endfunction

  virtual function int instMemWrites();
    return tb_lca_system.i_dummy_imemory.cnt_wr;
  endfunction
  virtual function int instrMemReads();
    return tb_lca_system.i_dummy_imemory.cnt_rd;
  endfunction
  virtual function int dataMemWrites();
    return tb_lca_system.i_dummy_dmemory.cnt_wr;
  endfunction
  virtual function int dataMemReads();
    return tb_lca_system.i_dummy_dmemory.cnt_rd;
  endfunction
  virtual function int stackMemWrites();
    return tb_lca_system.i_dummy_stack_memory.cnt_wr;
  endfunction
  virtual function int stackMemReads();
    return tb_lca_system.i_dummy_stack_memory.cnt_rd;
  endfunction
  virtual function int instrMemLatency();
    return m_instrMemLatency;
  endfunction
  virtual function string strInfo();
    /**
  ** avoid spaces in the string
  **/
    return "LCA_SPM";
  endfunction
endclass

module tb_lca_system (
    input logic clk_i,
    input logic rst_ni,
    input logic fetch_enable_i

);
  import redmule_pkg::*;
  import isolde_tcdm_pkg::*;
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
  localparam int unsigned HCI_AW = redmule_pkg::ADDR_W;
  localparam int unsigned HCI_DW = redmule_pkg::DATA_W;
  localparam int unsigned MP = HCI_DW / 32;
  localparam int unsigned MEMORY_SIZE = 32'h30000;
  localparam int unsigned STACK_MEMORY_SIZE = 32'h30000;
  localparam int unsigned PULP_XPULP = 1;
  localparam int unsigned FPU = 0;
  localparam int unsigned PULP_ZFINX = 0;
  localparam int unsigned N_TCDM_BANKS = HCI_DW / 32;



  localparam rule_addr_t BASE_ADDR = 32'h1c000000;
  localparam rule_addr_t HWPE_ADDR_BASE_BIT = 20;

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
  localparam rule_addr_t IMEM_ADDR = 32'h00100000;
  localparam int unsigned IMEM_SIZE = 32'h08000;
  localparam rule_addr_t DMEM_ADDR = 32'h00110000;
  localparam int unsigned DMEM_SIZE = 32'h30000;
  localparam rule_addr_t SMEM_ADDR = 32'h00140000;
  localparam int unsigned SMEM_SIZE = 32'h30000;
  localparam int unsigned GMEM_SIZE = SMEM_ADDR + SMEM_SIZE - IMEM_ADDR;
  //  see reset vector in cv32e40p/bsp/crt0.S
  localparam rule_addr_t BOOT_ADDR = 32'h00100080;
  localparam rule_addr_t PERIPH_ADDR = 32'h00001000;
  //see cv32e40p/bsp/simple_system_regs.h
  localparam rule_addr_t MMIO_ADDR = 32'h8000_0000;
  localparam rule_addr_t MMIO_ADDR_END = 32'h8000_0080;
  ;
  //debugger module
  localparam rule_addr_t DEBUG_ADDR = 32'h1A11_0000;
  localparam int unsigned DEBUG_SIZE = 32'h0000_1000;
  //spm narrow port start
  localparam rule_addr_t SPM_NARROW_ADDR = 32'h8000_1000;
  localparam int unsigned SPM_NARROW_SIZE = 32'h0000_1000;  //64kB

  /********************************************************/
  /**          Router configuratiion                     **/
  /*******************************************************/

  typedef enum {

    PERIPH_IDX,
    DATA_IDX,
    STACK_IDX,
    MMIO_IDX,
    SPM_IDX,
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
  };


  // global signals
  string stim_instr, stim_data;
  logic                               test_mode;
  //
  logic                               redmule_busy;

  logic                               sim_exit;
  MemStatisticsCallback               mem_stats_cb;

  logic                 [NC-1:0][1:0] evt;
  logic                               core_sleep;

  /********************************************************/
  /**           VERILATOR BUG                            **/
  /*******************************************************/

  //hwpe_ctrl_intf_periph #(.ID_WIDTH(ID)) periph (.clk(clk_i));
  /**
  * Bug in Verilator?! 
  * Verilator 5.036 2025-04-27 rev v5.036
  %Error-UNSUPPORTED: /home/dan/ibex/isolde/lca_system/.bender/git/checkouts/hwpe-stream-8301a9eab8e707b9/rtl/tcdm/hwpe_stream_tcdm_fifo_store.sv:82:32: Unsupported: Interfaced port on top level module
   82 |   hwpe_stream_intf_tcdm.slave  tcdm_slave,
      |                                ^~~~~~~~~~
                    ... For error description see https://verilator.org/warn/UNSUPPORTED?v=5.036
  %Error: /home/dan/ibex/isolde/lca_system/.bender/git/checkouts/hwpe-stream-8301a9eab8e707b9/rtl/tcdm/hwpe_stream_tcdm_fifo_store.sv:82:3: Parent instance's interface is not found: 'hwpe_stream_intf_tcdm'
* FIX: declare a dummy hwpe_stream_intf_tcdm variable
*/
  hwpe_stream_intf_tcdm dummy_intf (
      .clk(clk_i)
  );  // dummy interface for hwpe_stream_tcdm_fifo_store


  /********************************************************/
  /**           Interface Definitions                   **/
  /*******************************************************/

  hci_core_intf #(.DW(HCI_DW)) redmule_hci (.clk(clk_i));


  // ===  Memory banks  connections ===
  isolde_tcdm_pkg::req_t mem_req[N_TCDM_BANKS-1:0];
  isolde_tcdm_pkg::rsp_t mem_rsp[N_TCDM_BANKS-1:0];

  // === Data port ===
  isolde_tcdm_if tcdm_core_data ();
  isolde_tcdm_if tcdm_dmemory ();
  isolde_tcdm_if tcdm_dmemory_shim ();
  isolde_tcdm_if tcdm_spm_narrow ();  // narrow scratchpad memory interface

  // === hardware accelerator HWE port ===

  isolde_tcdm_if redmule_ctrl ();  // HWE peripheral  interface

  // === stack memory port ===
  isolde_tcdm_if tcdm_stack ();
  isolde_tcdm_if tcdm_stack_shim ();

  // === instruction memory port ===
  isolde_tcdm_if tcdm_core_inst ();
  isolde_tcdm_if tcdm_imem_shim ();

  // === Performermance counters & simulation control===
  isolde_tcdm_if tcdm_perfCountersSim ();

  // === Network on Chio NoC interfaces ===
  isolde_tcdm_pkg::req_t noc_reqs[LAST_IDX];
  isolde_tcdm_pkg::rsp_t noc_rsps[LAST_IDX];



  /********************************************************/
  /**           Router                                  **/
  /*******************************************************/

  isolde_router #(
      .N_RULES(NoRules),
      .ADDR_RANGES(addr_map)
  ) i_isolde_router (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(tcdm_core_data),
      .req_o       (noc_reqs),
      .rsp_i       (noc_rsps)
  );

  /********************************************************/
  /**           Performance counters                     **/
  /*******************************************************/

  assign tcdm_perfCountersSim.req = noc_reqs[MMIO_IDX];
  assign noc_rsps[MMIO_IDX] = tcdm_perfCountersSim.rsp;

  perfCounters #(
      .MMIO_ADDR(MMIO_ADDR)
  ) i_perfcnt (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(tcdm_perfCountersSim),
      .sim_exit_o(sim_exit),
      .mem_statistics_cb(mem_stats_cb)

  );

  always_comb begin
    if (sim_exit) begin
      endSimulation(tcdm_perfCountersSim.rsp.data);
    end
  end


  /********************************************************/
  /**     TCDM                                           **/
  /*******************************************************/

  assign tcdm_spm_narrow.req = noc_reqs[SPM_IDX];
  assign noc_rsps[SPM_IDX]   = tcdm_spm_narrow.rsp;

  isolde_tcdm_if tcdm_inter_dma ();

  // === Memory banks ===
  generate
    for (genvar i = 0; i < N_TCDM_BANKS; i++) begin : gen_mem
      // Instantiate memory bank
      tb_sram_mem #(
          .ID(i)
      ) i_bank (
          .clk_i,
          .rst_ni,
          .req_i(mem_req[i:i]),
          .rsp_o(mem_rsp[i:i])
      );
    end
  endgenerate

  isolde_addr_shim #(
      .START_ADDR(SPM_NARROW_ADDR),  // Set start address
      .END_ADDR(SPM_NARROW_ADDR + SPM_NARROW_SIZE)  // Set end address
  ) i_tcdm_inter_dma_shim (
      .tcdm_slave_i (tcdm_spm_narrow),
      .tcdm_master_o(tcdm_inter_dma)
  );

  isolde_tcdm_interconnect #(
      .ALIGN(1'b0),
      .HCI_DW(HCI_DW)
  ) i_tcdm_interconnect (
      .clk_i,
      .rst_ni,
      .s_hci_core (redmule_hci),
      .s_tcdm_core(tcdm_inter_dma),
      .mem_req_o  (mem_req),
      .mem_rsp_i  (mem_rsp)
  );

  /********************************************************/
  /**     Data memory                                    **/
  /*******************************************************/

  assign tcdm_dmemory.req   = noc_reqs[DATA_IDX];
  assign noc_rsps[DATA_IDX] = tcdm_dmemory.rsp;

  //   isolde_addr_shim #(
  //       .START_ADDR(DMEM_ADDR),  // Set start address
  //       .END_ADDR(DMEM_ADDR + DMEM_SIZE)  // Set end address
  //   ) i_dmem_shim (
  //       .tcdm_slave_i (tcdm_dmemory),
  //       .tcdm_master_o(tcdm_dmemory_shim)
  //   );

  tb_tcdm_mem #(
      .MEMORY_SIZE(GMEM_SIZE),
      .BASE_ADDR  (IMEM_ADDR)
  ) i_dummy_dmemory (
      .clk_i,
      .rst_ni,
      //.tcdm_slave_i(tcdm_dmemory_shim)
      .tcdm_slave_i(tcdm_dmemory)
  );

  /********************************************************/
  /**     Instruction memory                             **/
  /*******************************************************/

  isolde_addr_shim #(
      .START_ADDR(IMEM_ADDR),  // Set start address
      .END_ADDR(IMEM_ADDR + GMEM_SIZE)  // Set end address
  ) i_imem_shim (
      .tcdm_slave_i (tcdm_core_inst),
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


  /********************************************************/
  /**     Stack memory                                   **/
  /*******************************************************/

  assign tcdm_stack.req = noc_reqs[STACK_IDX];
  assign noc_rsps[STACK_IDX] = tcdm_stack.rsp;

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
  ) core_xif ();

  xif_monitor_cpu_issue xif_monitor_cpu_issue_i (
      clk_i,
      core_xif
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

  /********************************************************/
  /**     Hardware Engine HWE                            **/
  /*******************************************************/

  assign redmule_ctrl.req = noc_reqs[PERIPH_IDX];
  assign noc_rsps[PERIPH_IDX] = redmule_ctrl.rsp;

  isolde_redmule_top #(
      .ID_WIDTH (ID),
      .N_CORES  (NC),
      .DW       (HCI_DW),  // TCDM port dimension (in bits
      .AddrWidth(HCI_AW)
  ) i_redmule_top (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .test_mode_i   (test_mode),
      .fetch_enable_i(fetch_enable_i),
      .evt_o         (evt),
      .m_hci_core    (redmule_hci),
      .s_tcdm_ctrl   (redmule_ctrl)
  );
  isolde_hci_monitor #(
    .AW(HCI_AW),
    .DW(HCI_DW),
      .NAME("spm_hci_monitor")
  ) i_hci_monitor (
      .clk_i,
      .rst_ni,
      .hci_core(redmule_hci)
  );
  /********************************************************/

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

    $finish;
  endtask


  initial begin
    integer id;
    int cnt_rd, cnt_wr;
    MyCallback i_callback = new(IMEM_LATENCY);
    mem_stats_cb = i_callback;
    fh = $fopen("rtl_debug_trace.log", "w");

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
  end
endmodule  // tb_lca_system
