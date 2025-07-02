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
    return "LCA";
  endfunction
endclass

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
  localparam rule_addr_t PERI_ADDR = 32'h00001000;
  //see cv32e40p/bsp/simple_system_regs.h
  localparam rule_addr_t MMIO_ADDR = 32'h8000_0000;
  localparam rule_addr_t MMIO_ADDR_END = 32'h8000_0080;
  ;
  //debugger module
  localparam rule_addr_t DEBUG_ADDR = 32'h1A11_0000;
  localparam int unsigned DEBUG_SIZE = 32'h0000_1000;

  typedef struct packed {
    rule_idx_t  idx;
    rule_addr_t start_addr;
    rule_addr_t end_addr;
  } tb_rule_t;

  localparam int unsigned NoRules = 5;
  localparam int unsigned NoIndices = LAST_IDX;
  // 
  localparam tb_rule_t [NoRules-1:0] addr_map = '{
      '{idx: PERIPH_IDX, start_addr: PERI_ADDR, end_addr: IMEM_ADDR},
      '{idx: DATA_IDX, start_addr: DMEM_ADDR, end_addr: DMEM_ADDR + DMEM_SIZE},
      '{idx: STACK_IDX, start_addr: SMEM_ADDR, end_addr: SMEM_ADDR + SMEM_SIZE},
      '{idx: MMIO_IDX, start_addr: MMIO_ADDR, end_addr: MMIO_ADDR_END},
      '{idx: DEBUG_IDX, start_addr: DEBUG_ADDR, end_addr: DEBUG_ADDR + DEBUG_SIZE}
  };


  // global signals
  string stim_instr, stim_data;
  logic                          test_mode;
  //
  logic                          redmule_busy;

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

  hwpe_stream_intf_tcdm tcdm[MP:0] (.clk(clk_i));

  isolde_tcdm_if tcdm_core_data ();
  isolde_tcdm_if tcdm_data_dm ();
  isolde_tcdm_if tcdm_data_dm_mux ();

  isolde_tcdm_if tcdm_stack ();
  isolde_tcdm_if tcdm_stack_shim ();

  isolde_tcdm_if tcdm_core_inst ();
  isolde_tcdm_if tcdm_imem_shim ();

  //
  isolde_tcdm_if tcdm_perfCountersSim ();
  logic sim_exit;

  MemStatisticsCallback mem_stats_cb;
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
        tcdm_stack.req = tcdm_core_data.req;
      end
      MMIO_IDX:   tcdm_perfCountersSim.req = tcdm_core_data.req;
      DEBUG_IDX: begin  //bind_debug module
        tcdm_data_dm.req = tcdm_core_data.req;
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
        MMIO_IDX: tcdm_core_data.rsp.gnt = tcdm_perfCountersSim.rsp.gnt;
        DEBUG_IDX: tcdm_core_data.rsp.gnt = tcdm_data_dm.rsp.gnt;
        default: tcdm_core_data.rsp.gnt = '0;
      endcase
    end
  end

  assign tcdm_core_data.rsp.valid = periph.r_valid | tcdm_stack.rsp.valid | tcdm_data_dm.rsp.valid | tcdm[MP].r_valid | tcdm_perfCountersSim.rsp.valid;

  always_comb begin

    case (rsp_idx)
      PERIPH_IDX: tcdm_core_data.rsp.data = periph.r_data;
      DATA_IDX: tcdm_core_data.rsp.data = tcdm[MP].r_data;
      STACK_IDX: tcdm_core_data.rsp.data = tcdm_stack.rsp.data;
      MMIO_IDX: tcdm_core_data.rsp.data = tcdm_perfCountersSim.rsp.data;
      DEBUG_IDX: tcdm_core_data.rsp.data = tcdm_data_dm.rsp.data;
      default: tcdm_core_data.rsp.data = '0;
    endcase
  end

  hci_core_intf #(.DW(DW)) redmule_tcdm (.clk(clk_i));
  hwpe_ctrl_intf_periph #(.ID_WIDTH(ID)) periph (.clk(clk_i));

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
