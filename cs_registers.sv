////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Sven Stucki - svstucki@student.ethz.ch.ch                  //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Create Date:    25/05/2015                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    cs_registers.sv                                            //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Control and Status Registers (CSRs) loosely following the  //
//                 RiscV draft priviledged instruction set spec (v1.7)        //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"


module riscv_cs_registers
#(
  parameter N_EXT_PERF_COUNTERS = 0
)
(
  // Clock and Reset
  input logic         clk,
  input logic         rst_n,

  // Core and Cluster ID
  input logic   [4:0] core_id_i,
  input logic   [4:0] cluster_id_i,

  // Interface to registers (SRAM like)
  input logic  [11:0] csr_addr_i,
  input logic  [31:0] csr_wdata_i,
  input logic   [1:0] csr_op_i,
  output logic [31:0] csr_rdata_o,

  // Interrupts
  input logic  [31:0] curr_pc_if_i,
  input logic  [31:0] curr_pc_id_i,
  input logic         save_pc_if_i,
  input logic         save_pc_id_i,

  output logic        irq_enable_o,
  output logic [31:0] epcr_o,

  // Performance Counters
  input  logic        id_valid_i,        // ID stage is done
  input  logic        is_compressed_i,   // compressed instruction in ID
  input  logic        is_decoding_i,     // controller is in DECODE state

  input  logic        imiss_i,           // instruction fetch
  input  logic        jump_i,            // jump instruction seen   (j, jr, jal, jalr)
  input  logic        branch_i,          // branch instruction seen (bf, bnf)
  input  logic        ld_stall_i,        // load use hazard
  input  logic        jr_stall_i,        // jump register use hazard

  input  logic        mem_load_i,        // load from memory in this cycle
  input  logic        mem_store_i,       // store to memory in this cycle

  input  logic [N_EXT_PERF_COUNTERS-1:0]   ext_counters_i
);

  localparam N_PERF_COUNTERS = 10 + N_EXT_PERF_COUNTERS;

`ifdef PULP_FPGA_EMUL
  localparam N_PERF_REGS     = N_PERF_COUNTERS;
`elsif SYNTHESIS
  localparam N_PERF_REGS     = 1;
`else
  localparam N_PERF_REGS     = N_PERF_COUNTERS;
`endif

  // Performance Counter Signals
  logic                          id_valid_q;
  logic [N_PERF_COUNTERS-1:0]    PCCR_in;  // input signals for each counter category
  logic [N_PERF_COUNTERS-1:0]    PCCR_inc, PCCR_inc_q; // should the counter be increased?

  logic [N_PERF_REGS-1:0] [31:0] PCCR_q, PCCR_n; // performance counters counter register
  logic [1:0]                    PCMR_n, PCMR_q; // mode register, controls saturation and global enable
  logic [N_PERF_COUNTERS-1:0]    PCER_n, PCER_q; // selected counter input

  logic [31:0]                   perf_rdata;
  logic [4:0]                    pccr_index;
  logic                          pccr_all_sel;
  logic                          is_pccr;
  logic                          is_pcer;
  logic                          is_pcmr;

  // Generic CSRs
  logic [31:0] csr [0:`CSR_MAX_IDX];
  logic [31:0] csr_n [0:`CSR_MAX_IDX];

  // CSR update logic
  logic [31:0] csr_wdata_int;
  logic [31:0] csr_rdata_int;
  logic        csr_we_int;

  // Interrupt control signals
  logic irq_enable, irq_enable_n;


  ////////////////////////////////////////////
  //   ____ ____  ____    ____              //
  //  / ___/ ___||  _ \  |  _ \ ___  __ _   //
  // | |   \___ \| |_) | | |_) / _ \/ _` |  //
  // | |___ ___) |  _ <  |  _ <  __/ (_| |  //
  //  \____|____/|_| \_\ |_| \_\___|\__, |  //
  //                                |___/   //
  ////////////////////////////////////////////

  // read logic
  always_comb
  begin
    csr_rdata_int = 'x;

    case (csr_addr_i)
      // mstatus: always M-mode, contains IE bit
      12'h300: csr_rdata_int = {29'b0, 2'b11, irq_enable};

      // mscratch
      12'h340: csr_rdata_int = csr[`CSR_IDX_MSCRATCH];
      // mepc: exception program counter
      12'h341: csr_rdata_int = csr[`CSR_IDX_MEPC];

      // mcpuid: RV32I
      12'hF00: csr_rdata_int = 32'h00_00_01_00;
      // mimpid: PULP, anonymous source (no allocated ID yet)
      12'hF01: csr_rdata_int = 32'h00_00_80_00;
      // mhartid: unique hardware thread id
      12'hF10: csr_rdata_int = {22'b0, cluster_id_i, core_id_i};
    endcase
  end


  // write logic
  always_comb
  begin
    csr_n        = csr;
    irq_enable_n = irq_enable;

    case (csr_addr_i)
      // mstatus: IE bit
      12'h300: if (csr_we_int) irq_enable_n = csr_wdata_int[0];

      // mscratch
      12'h340: if (csr_we_int) csr_n[`CSR_IDX_MSCRATCH] = csr_wdata_int;
      // mepc: exception program counter
      12'h341: if (csr_we_int) csr_n[`CSR_IDX_MEPC] = csr_wdata_int;
    endcase
  end


  // CSR operation logic
  always_comb
  begin
    csr_wdata_int = csr_wdata_i;
    csr_we_int    = 1'b1;

    unique case (csr_op_i)
      `CSR_OP_WRITE: csr_wdata_int = csr_wdata_i;
      `CSR_OP_SET:   csr_wdata_int = csr_wdata_i | csr_rdata_o;
      `CSR_OP_CLEAR: csr_wdata_int = csr_wdata_i & ~(csr_rdata_o);

      `CSR_OP_NONE: begin
        csr_wdata_int = csr_wdata_i;
        csr_we_int    = 1'b0;
      end
    endcase
  end


  // output mux
  always_comb
  begin
    csr_rdata_o = csr_rdata_int;

    // performance counters
    if (is_pccr || is_pcer || is_pcmr)
      csr_rdata_o = perf_rdata;
  end


  // directly output some registers
  assign irq_enable_o = irq_enable;
  assign epcr_o       = csr[`CSR_IDX_MEPC];


  // actual registers
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
    begin
      csr        <= '{default: 32'b0};
      irq_enable <= 1'b0;
    end
    else
    begin
      // update CSRs
      csr                 <= csr_n;

      irq_enable <= irq_enable_n;
      // exception PC writes from exception controller get priority
      if (save_pc_if_i == 1'b1)
        csr[`CSR_IDX_MEPC] <= curr_pc_if_i;
      else if (save_pc_id_i == 1'b1)
        csr[`CSR_IDX_MEPC] <= curr_pc_id_i;
    end
  end

  /////////////////////////////////////////////////////////////////
  //   ____            __     ____                  _            //
  // |  _ \ ___ _ __ / _|   / ___|___  _   _ _ __ | |_ ___ _ __  //
  // | |_) / _ \ '__| |_   | |   / _ \| | | | '_ \| __/ _ \ '__| //
  // |  __/  __/ |  |  _|  | |__| (_) | |_| | | | | ||  __/ |    //
  // |_|   \___|_|  |_|(_)  \____\___/ \__,_|_| |_|\__\___|_|    //
  //                                                             //
  /////////////////////////////////////////////////////////////////

  assign PCCR_in[0]  = 1'b1;                          // cycle counter
  assign PCCR_in[1]  = id_valid_i & is_decoding_i;    // instruction counter
  assign PCCR_in[2]  = ld_stall_i & id_valid_q;       // nr of load use hazards
  assign PCCR_in[3]  = jr_stall_i & id_valid_q;       // nr of jump register hazards
  assign PCCR_in[4]  = imiss_i;                       // cycles waiting for instruction fetches
  assign PCCR_in[5]  = mem_load_i;                    // nr of loads
  assign PCCR_in[6]  = mem_store_i;                   // nr of stores
  assign PCCR_in[7]  = jump_i     & id_valid_q;       // nr of jumps (unconditional)
  assign PCCR_in[8]  = branch_i   & id_valid_q;       // nr of branches (conditional)
  assign PCCR_in[9]  = id_valid_i & is_decoding_i & is_compressed_i;  // compressed instruction counter

  // assign external performance counters
  generate
    genvar i;
    for(i = 0; i < N_EXT_PERF_COUNTERS; i++)
    begin
      assign PCCR_in[N_PERF_COUNTERS - N_EXT_PERF_COUNTERS + i] = ext_counters_i[i];
    end
  endgenerate

  // address decoder for performance counter registers
  always_comb
  begin
    is_pccr      = 1'b0;
    is_pcmr      = 1'b0;
    is_pcer      = 1'b0;
    pccr_all_sel = 1'b0;
    pccr_index   = '0;
    perf_rdata   = '0;

    unique case (csr_addr_i)
      12'h7A0: begin
        is_pcer = 1'b1;
        perf_rdata[N_PERF_COUNTERS-1:0] = PCER_q;
      end
      12'h7A1: begin
        is_pcmr = 1'b1;
        perf_rdata[1:0] = PCMR_q;
      end
      12'h79F: begin
        is_pccr = 1'b1;
        pccr_all_sel = 1'b1;
      end
      default:;
    endcase

    // look for 780 to 79F, Performance Counter Counter Registers
    if (csr_addr_i[11:5] == 7'b0111100) begin
      is_pccr     = 1'b1;

      pccr_index = csr_addr_i[4:0];

      perf_rdata = PCCR_q[csr_addr_i[4:0]];
    end
  end


  // performance counter counter update logic
`ifdef SYNTHESIS
  // for synthesis we just have one performance counter register
  assign PCCR_inc[0] = (|(PCCR_in & PCER_q)) & PCMR_q[0];

  always_comb
  begin
    PCCR_n[0]   = PCCR_q[0];

    if ((PCCR_inc_q[0] == 1'b1) && ((PCCR_q[0] != 32'hFFFFFFFF) || (PCMR_q[1] == 1'b0)))
      PCCR_n[0] = PCCR_q[0] + 1;

    if (is_pccr == 1'b1) begin
      unique case (csr_op_i)
        `CSR_OP_NONE:   ;
        `CSR_OP_WRITE:  PCCR_n[0] = csr_wdata_i;
        `CSR_OP_SET:    PCCR_n[0] = csr_wdata_i | PCCR_q[0];
        `CSR_OP_CLEAR:  PCCR_n[0] = csr_wdata_i & ~(PCCR_q[0]);
      endcase
    end
  end
`else
  always_comb
  begin
    for(int i = 0; i < N_PERF_COUNTERS; i++)
    begin : PERF_CNT_INC
      PCCR_inc[i] = PCCR_in[i] & PCER_q[i] & PCMR_q[0];

      PCCR_n[i]   = PCCR_q[i];

      if ((PCCR_inc_q[i] == 1'b1) && ((PCCR_q[i] != 32'hFFFFFFFF) || (PCMR_q[1] == 1'b0)))
        PCCR_n[i] = PCCR_q[i] + 1;

      if (is_pccr == 1'b1 && (pccr_all_sel == 1'b1 || pccr_index == i)) begin
        unique case (csr_op_i)
          `CSR_OP_NONE:   ;
          `CSR_OP_WRITE:  PCCR_n[i] = csr_wdata_i;
          `CSR_OP_SET:    PCCR_n[i] = csr_wdata_i | PCCR_q[i];
          `CSR_OP_CLEAR:  PCCR_n[i] = csr_wdata_i & ~(PCCR_q[i]);
        endcase
      end
    end
  end
`endif

  // update PCMR and PCER
  always_comb
  begin
    PCMR_n = PCMR_q;
    PCER_n = PCER_q;

    if (is_pcmr) begin
      unique case (csr_op_i)
        `CSR_OP_NONE:   ;
        `CSR_OP_WRITE:  PCMR_n = csr_wdata_i[1:0];
        `CSR_OP_SET:    PCMR_n = csr_wdata_i[1:0] | PCMR_q;
        `CSR_OP_CLEAR:  PCMR_n = csr_wdata_i[1:0] & ~(PCMR_q);
      endcase
    end

    if (is_pcer) begin
      unique case (csr_op_i)
        `CSR_OP_NONE:   ;
        `CSR_OP_WRITE:  PCER_n = csr_wdata_i[N_PERF_REGS-1:0];
        `CSR_OP_SET:    PCER_n = csr_wdata_i[N_PERF_REGS-1:0] | PCER_q;
        `CSR_OP_CLEAR:  PCER_n = csr_wdata_i[N_PERF_REGS-1:0] & ~(PCER_q);
      endcase
    end
  end

  // Performance Counter Registers
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
    begin
      id_valid_q <= 1'b0;

      PCER_q <= 'h0;
      PCMR_q <= 2'h3;

      for(int i = 0; i < N_PERF_REGS; i++)
      begin
        PCCR_q[i]     <= '0;
        PCCR_inc_q[i] <= '0;
      end
    end
    else
    begin
      id_valid_q <= id_valid_i;

      PCER_q <= PCER_n;
      PCMR_q <= PCMR_n;

      for(int i = 0; i < N_PERF_REGS; i++)
      begin
        PCCR_q[i]     <= PCCR_n[i];
        PCCR_inc_q[i] <= PCCR_inc[i];
      end

    end
  end

endmodule
