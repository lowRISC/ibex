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
`ifdef TARGET_RV_DEBUG
    return "LCA_SPM_DEBUG";
`else
    return "LCA_SPM";
`endif
  endfunction
endclass

module tb_lca_system (
    input logic clk_i,
    input logic rst_ni,
    input logic fetch_enable_i

);
  import redmule_pkg::*;
  import isolde_tcdm_pkg::*;
  import aida_lca_package::*;
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




  int fh;  //filehandle
  //

  // global signals
  string stim_instr, stim_data;

  logic                                          sim_exit;
  logic                 [                  31:0] sim_exit_code;
  MemStatisticsCallback                          mem_stats_cb;



  /********************************************************/
  /**           Debug module signals                     **/
  /*******************************************************/
  logic                 [                  31:0] sim_jtag_exit;
  jtag_pkg::jtag_req_t                           jtag_in;
  jtag_pkg::jtag_rsp_t                           jtag_out;
  logic                 [rv_dm_pkg::NrHarts-1:0] debug_req;
  // === JTAG simulation parameters
  localparam int unsigned OPENOCD_PORT = 9999;








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
  // ===  Memory banks  connections ===
  isolde_tcdm_pkg::req_t mem_req[N_TCDM_BANKS-1:0];
  isolde_tcdm_pkg::rsp_t mem_rsp[N_TCDM_BANKS-1:0];

  // === instruction memory port ===
  isolde_tcdm_if aida_instr_memory ();

  // === Data port ===
  isolde_tcdm_if aida_data_memory ();

  // === stack memory port ===
  isolde_tcdm_if aida_stack_memory ();

  // === memory mapped I/O ports ===
  isolde_tcdm_if aida_mmio ();

  /********************************************************/
  /**           Performance counters                     **/
  /*******************************************************/
  perfCounters #(
      .MMIO_ADDR(MMIO_ADDR)
  ) i_perfcnt (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(aida_mmio),
      .sim_exit_o(sim_exit),
      .sim_exit_code_o(sim_exit_code),
      .mem_statistics_cb(mem_stats_cb)

  );
`ifndef TARGET_RV_DEBUG
  always_comb begin
    if (sim_exit) begin
      endSimulation(sim_exit_code);
    end
  end
`endif

`ifdef TARGET_RV_DEBUG
  /********************************************************/
  /**     JTAG simulation                                **/
  /*******************************************************/
  SimJTAG #(
      .TICK_DELAY(1),
      .PORT(OPENOCD_PORT)
  ) i_sim_jtag (
      .clock          (clk_i),
      .reset          (~rst_ni),
      .enable         (1'b1),
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
    if (sim_jtag_exit) endSimulation(sim_exit_code);
  end
`endif


  /********************************************************/
  /**     Data memory                                    **/
  /*******************************************************/
  tb_tcdm_mem #(
      .MEMORY_SIZE(GMEM_SIZE)
  ) i_dummy_dmemory (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(aida_data_memory)
  );

  /********************************************************/
  /**     Instruction memory                             **/
  /*******************************************************/
  tb_tcdm_mem #(
      .MEMORY_SIZE (GMEM_SIZE),
      .DELAY_CYCLES(IMEM_LATENCY)
  ) i_dummy_imemory (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(aida_instr_memory)
  );


  /********************************************************/
  /**     Stack memory                                   **/
  /*******************************************************/
  tb_tcdm_mem #(
      .MEMORY_SIZE(SMEM_SIZE)
  ) i_dummy_stack_memory (
      .clk_i,
      .rst_ni,
      .tcdm_slave_i(aida_stack_memory)
  );


  /********************************************************/
  /**     TCDM                                           **/
  /*******************************************************/

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


  /********************************************************/
  /**    aida core                                      **/
  /*******************************************************/

  aida_lca #(
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
  ) i_aida_lca (
      .clk_i,
      .rst_ni,
      .fetch_enable_i,
      .aida_data_memory,
      .aida_stack_memory,
      .aida_instr_memory,
      .aida_mmio,
      .spm_req_o(mem_req),
      .spm_rsp_i(mem_rsp),
      .aida_jtag_in (jtag_in),
      .aida_jtag_out(jtag_out)

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


  end

  // close output file for writing
  final begin
    $fclose(fh);
  end
endmodule  // tb_lca_system
