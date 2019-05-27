// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Control and Status Registers                               //
// Project Name:   ibex                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Control and Status Registers (CSRs) loosely following the  //
//                 RiscV draft priviledged instruction set spec (v1.9)        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

/**
 * Control and Status Registers
 *
 * Control and Status Registers (CSRs) loosely following the RiscV draft
 * priviledged instruction set spec (v1.9)
 */
module ibex_cs_registers #(
    parameter int unsigned NumExtCounters = 0,
    parameter bit RV32E                   = 0,
    parameter bit RV32M                   = 0
) (
    // Clock and Reset
    input  logic                      clk_i,
    input  logic                      rst_ni,

    // Core and Cluster ID
    input  logic  [3:0]               core_id_i,
    input  logic  [5:0]               cluster_id_i,

    input  logic [31:0]               boot_addr_i,

    // Interface to registers (SRAM like)
    input  logic                      csr_access_i,
    input  ibex_defines::csr_num_e    csr_addr_i,
    input  logic [31:0]               csr_wdata_i,
    input  ibex_defines::csr_op_e     csr_op_i,
    output logic [31:0]               csr_rdata_o,

    // Interrupts
    output logic                      m_irq_enable_o,
    output logic [31:0]               mepc_o,

    // debug
    input  ibex_defines::dbg_cause_e  debug_cause_i,
    input  logic                      debug_csr_save_i,
    output logic [31:0]               depc_o,
    output logic                      debug_single_step_o,
    output logic                      debug_ebreakm_o,

    input  logic [31:0]               pc_if_i,
    input  logic [31:0]               pc_id_i,

    input  logic                      csr_save_if_i,
    input  logic                      csr_save_id_i,
    input  logic                      csr_restore_mret_i,
    input  logic                      csr_restore_dret_i,

    input  ibex_defines::exc_cause_e  csr_cause_i,
    input  logic                      csr_save_cause_i,

    // Performance Counters
    input  logic                      if_valid_i,        // IF stage gives a new instr
    input  logic                      id_valid_i,        // ID stage is done
    input  logic                      is_compressed_i,   // compressed instr in ID
    input  logic                      is_decoding_i,     // controller is in DECODE state

    input  logic                      imiss_i,           // instr fetch
    input  logic                      pc_set_i,          // pc was set to a new value
    input  logic                      jump_i,            // jump instr seen (j, jr, jal, jalr)
    input  logic                      branch_i,          // branch instr seen (bf, bnf)
    input  logic                      branch_taken_i,    // branch was taken
    input  logic                      mem_load_i,        // load from memory in this cycle
    input  logic                      mem_store_i,       // store to memory in this cycle
    input  logic [NumExtCounters-1:0] ext_counters_i
);

  import ibex_defines::*;

  // misa
  localparam logic [1:0] MXL = 2'd1; // M-XLEN: XLEN in M-Mode for RV32
  localparam logic [31:0] MISA_VALUE =
      (0     <<  0)  // A - Atomic Instructions extension
    | (1     <<  2)  // C - Compressed extension
    | (0     <<  3)  // D - Double precision floating-point extension
    | (RV32E <<  4)  // E - RV32E base ISA
    | (0     <<  5)  // F - Single precision floating-point extension
    | (1     <<  8)  // I - RV32I/64I/128I base ISA
    | (RV32M << 12)  // M - Integer Multiply/Divide extension
    | (0     << 13)  // N - User level interrupts supported
    | (0     << 18)  // S - Supervisor mode implemented
    | (0     << 20)  // U - User mode implemented
    | (0     << 23)  // X - Non-standard extensions present
    | (MXL   << 30); // M-XLEN

  localparam int unsigned N_PERF_COUNTERS = 11 + NumExtCounters;

`ifdef ASIC_SYNTHESIS
  localparam N_PERF_REGS     = 1;
`else
  localparam N_PERF_REGS     = N_PERF_COUNTERS;
`endif

  `define MSTATUS_UIE_BITS        0
  `define MSTATUS_SIE_BITS        1
  `define MSTATUS_MIE_BITS        3
  `define MSTATUS_UPIE_BITS       4
  `define MSTATUS_SPIE_BITS       5
  `define MSTATUS_MPIE_BITS       7
  `define MSTATUS_SPP_BITS        8
  `define MSTATUS_MPP_BITS    12:11

  typedef struct packed {
    //logic uie;       - unimplemented, hardwired to '0
    // logic sie;      - unimplemented, hardwired to '0
    // logic hie;      - unimplemented, hardwired to '0
    logic mie;
    //logic upie;     - unimplemented, hardwired to '0
    // logic spie;     - unimplemented, hardwired to '0
    // logic hpie;     - unimplemented, hardwired to '0
    logic mpie;
    // logic spp;      - unimplemented, hardwired to '0
    // logic[1:0] hpp; - unimplemented, hardwired to '0
    priv_lvl_e mpp;
  } Status_t;

  typedef struct packed {
      x_debug_ver_e xdebugver;
      logic [11:0]  zero2;
      logic         ebreakm;
      logic         zero1;
      logic         ebreaks;
      logic         ebreaku;
      logic         stepie;
      logic         stopcount;
      logic         stoptime;
      dbg_cause_e   cause;
      logic         zero0;
      logic         mprven;
      logic         nmip;
      logic         step;
      priv_lvl_e    prv;
  } Dcsr_t;


  // Performance Counter Signals
  logic [N_PERF_COUNTERS-1:0]    PCCR_in;  // input signals for each counter category
  logic [N_PERF_COUNTERS-1:0]    PCCR_inc, PCCR_inc_q; // should the counter be increased?

  logic [N_PERF_REGS-1:0] [31:0] PCCR_q, PCCR_n; // performance counters counter register
  logic [1:0]                    PCMR_n, PCMR_q; // mode register, controls saturation and
                                                 // global enable
  logic [N_PERF_COUNTERS-1:0]    PCER_n, PCER_q; // selected counter input

  logic [31:0]                   perf_rdata;
  logic [4:0]                    pccr_index;
  logic                          pccr_all_sel;
  logic                          is_pccr;
  logic                          is_pcer;
  logic                          is_pcmr;

  // CSR update logic
  logic [31:0] csr_wdata_int;
  logic [31:0] csr_rdata_int;
  logic        csr_we_int;

  // Interrupt control signals
  logic [31:0] mepc_q, mepc_n;
  Dcsr_t       dcsr_q, dcsr_n;
  logic [31:0] depc_q, depc_n;
  logic [31:0] dscratch0_q, dscratch0_n;
  logic [31:0] dscratch1_q, dscratch1_n;
  logic [ 5:0] mcause_q, mcause_n;
  Status_t mstatus_q, mstatus_n;
  logic [31:0] exception_pc;

  /////////////
  // CSR reg //
  /////////////

  // read logic
  always_comb begin
    csr_rdata_int = '0;

    unique case (csr_addr_i)
      // mstatus: always M-mode, contains IE bit
      CSR_MSTATUS: begin
        csr_rdata_int = {
            19'b0,
            mstatus_q.mpp,
            3'b0,
            mstatus_q.mpie,
            3'h0,
            mstatus_q.mie,
            3'h0
        };
      end

      // mtvec: machine trap-handler base address
      CSR_MTVEC: csr_rdata_int = boot_addr_i;

      // mepc: exception program counter
      CSR_MEPC: csr_rdata_int = mepc_q;

      // mcause: exception cause
      CSR_MCAUSE: csr_rdata_int = {mcause_q[5], 26'b0, mcause_q[4:0]};

      // mhartid: unique hardware thread id
      CSR_MHARTID: csr_rdata_int = {21'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]};

      // misa
      CSR_MISA: csr_rdata_int = MISA_VALUE;

      CSR_DCSR: csr_rdata_int = dcsr_q;
      CSR_DPC: csr_rdata_int = depc_q;
      CSR_DSCRATCH0: csr_rdata_int = dscratch0_q;
      CSR_DSCRATCH1: csr_rdata_int = dscratch1_q;
      default:;
    endcase
  end

  // write logic
  always_comb begin
    mepc_n       = mepc_q;
    depc_n       = depc_q;
    dcsr_n       = dcsr_q;
    dscratch0_n  = dscratch0_q;
    dscratch1_n  = dscratch1_q;
    mstatus_n    = mstatus_q;
    mcause_n     = mcause_q;
    exception_pc = pc_id_i;

    unique case (csr_addr_i)
      // mstatus: IE bit
      CSR_MSTATUS: begin
        if (csr_we_int) begin
          mstatus_n = '{
              mie:  csr_wdata_int[`MSTATUS_MIE_BITS],
              mpie: csr_wdata_int[`MSTATUS_MPIE_BITS],
              mpp:  PRIV_LVL_M
          };
        end
      end
      // mepc: exception program counter
      CSR_MEPC: if (csr_we_int) mepc_n = csr_wdata_int;
      // mcause
      CSR_MCAUSE: if (csr_we_int) mcause_n = {csr_wdata_int[31], csr_wdata_int[4:0]};

      CSR_DCSR: begin
        if (csr_we_int) begin
          dcsr_n = csr_wdata_int;
          dcsr_n.xdebugver = XDEBUGVER_STD;
          dcsr_n.prv = PRIV_LVL_M; // only M-mode is supported

          // currently not supported:
          dcsr_n.nmip = 1'b0;
          dcsr_n.mprven = 1'b0;
          dcsr_n.stopcount = 1'b0;
          dcsr_n.stoptime = 1'b0;

          // forced to be zero
          dcsr_n.zero0 = 1'b0;
          dcsr_n.zero1 = 1'b0;
          dcsr_n.zero2 = 12'h0;
        end
      end

      CSR_DPC: begin
        // Only valid PC addresses are allowed (half-word aligned with C ext.)
        if (csr_we_int && csr_wdata_int[0] == 1'b0) begin
          depc_n = csr_wdata_int;
        end
      end

      CSR_DSCRATCH0: begin
        if (csr_we_int) begin
          dscratch0_n = csr_wdata_int;
        end
      end

      CSR_DSCRATCH1: begin
        if (csr_we_int) begin
          dscratch1_n = csr_wdata_int;
        end
      end

      default:;
    endcase

    // exception controller gets priority over other writes
    unique case (1'b1)

      csr_save_cause_i: begin
        unique case (1'b1)
          csr_save_if_i: begin
            exception_pc = pc_if_i;
          end
          csr_save_id_i: begin
            exception_pc = pc_id_i;
          end
          default:;
        endcase

        if (debug_csr_save_i) begin
          // all interrupts are masked, don't update cause, epc, tval dpc and
          // mpstatus
          dcsr_n.prv   = PRIV_LVL_M;
          dcsr_n.cause = debug_cause_i;
          depc_n       = exception_pc;
        end else begin
          mstatus_n.mpie = mstatus_q.mie;
          mstatus_n.mie  = 1'b0;
          mstatus_n.mpp  = PRIV_LVL_M;
          mepc_n         = exception_pc;
          mcause_n       = csr_cause_i;
        end
      end //csr_save_cause_i

      csr_restore_mret_i: begin //MRET
        mstatus_n.mie  = mstatus_q.mpie;
        mstatus_n.mpie = 1'b1;
      end //csr_restore_mret_i

      csr_restore_dret_i: begin //DRET
        mstatus_n.mie  = mstatus_q.mpie;
        mstatus_n.mpie = 1'b1;
      end //csr_restore_dret_i

      default:;
    endcase
  end


  // CSR operation logic
  always_comb begin
    csr_we_int    = 1'b1;

    unique case (csr_op_i)
      CSR_OP_WRITE: csr_wdata_int =  csr_wdata_i;
      CSR_OP_SET:   csr_wdata_int =  csr_wdata_i | csr_rdata_o;
      CSR_OP_CLEAR: csr_wdata_int = ~csr_wdata_i & csr_rdata_o;
      CSR_OP_NONE: begin
        csr_wdata_int = csr_wdata_i;
        csr_we_int    = 1'b0;
      end
      default: begin
        csr_wdata_int = 'X;
        csr_we_int    = 1'bX;
      end
    endcase
  end

  // output mux, possibly choose performance counters
  assign csr_rdata_o = (is_pccr || is_pcer || is_pcmr) ? perf_rdata : csr_rdata_int;

  // directly output some registers
  assign m_irq_enable_o  = mstatus_q.mie;
  assign mepc_o          = mepc_q;
  assign depc_o          = depc_q;

  assign debug_single_step_o  = dcsr_q.step;
  assign debug_ebreakm_o      = dcsr_q.ebreakm;

  // actual registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mstatus_q  <= '{
          mie:  1'b0,
          mpie: 1'b0,
          mpp:  PRIV_LVL_M
      };
      mepc_q     <= '0;
      mcause_q   <= '0;

      depc_q     <= '0;
      dcsr_q     <= '{
          xdebugver: XDEBUGVER_NO,   // 4'h0
          cause:     DBG_CAUSE_NONE, // 3'h0
          prv:       PRIV_LVL_M,
          default:   '0
      };
      dscratch0_q <= '0;
      dscratch1_q <= '0;
    end else begin
      // update CSRs
      mstatus_q  <= '{
          mie:  mstatus_n.mie,
          mpie: mstatus_n.mpie,
          mpp:  PRIV_LVL_M
      };
      mepc_q      <= mepc_n;
      mcause_q    <= mcause_n;

      depc_q      <= depc_n;
      dcsr_q      <= dcsr_n;
      dscratch0_q <= dscratch0_n;
      dscratch1_q <= dscratch1_n;
    end
  end

  //////////////////////////
  // Performance counters //
  //////////////////////////

  logic [$bits(csr_num_e)-1:0] csr_addr;

  assign csr_addr    = {csr_addr_i};

  assign PCCR_in[0]  = 1'b1;                          // cycle counter
  assign PCCR_in[1]  = if_valid_i;                    // instruction counter
  assign PCCR_in[2]  = 1'b0;                          // Reserved
  assign PCCR_in[3]  = 1'b0;                          // Reserved
  assign PCCR_in[4]  = imiss_i & (~pc_set_i);         // cycles waiting for instruction fetches,
                                                      // excluding jumps and branches
  assign PCCR_in[5]  = mem_load_i;                    // nr of loads
  assign PCCR_in[6]  = mem_store_i;                   // nr of stores
  assign PCCR_in[7]  = jump_i;                        // nr of jumps (unconditional)
  assign PCCR_in[8]  = branch_i;                      // nr of branches (conditional)
  assign PCCR_in[9]  = branch_taken_i;                // nr of taken branches (conditional)
  assign PCCR_in[10] = id_valid_i & is_decoding_i & is_compressed_i; // compressed intr ctr

  // assign external performance counters
  for (genvar i = 0; i < NumExtCounters; i++) begin : gen_ext_counters
    assign PCCR_in[N_PERF_COUNTERS - NumExtCounters + i] = ext_counters_i[i];
  end

  // address decoder for performance counter registers
  always_comb begin
    is_pccr      = 1'b0;
    is_pcmr      = 1'b0;
    is_pcer      = 1'b0;
    pccr_all_sel = 1'b0;
    pccr_index   = '0;
    perf_rdata   = '0;

    // only perform csr access if we actually care about the read data
    if (csr_access_i) begin
      unique case (csr_addr_i)
        CSR_TSELECT: begin
          is_pcer = 1'b1;
          perf_rdata[N_PERF_COUNTERS-1:0] = PCER_q;
        end
        CSR_TDATA1: begin
          is_pcmr = 1'b1;
          perf_rdata[1:0] = PCMR_q;
        end
        CSR_PCCR31: begin
          is_pccr = 1'b1;
          pccr_all_sel = 1'b1;
        end
        default:;
      endcase

      // look for 780 to 79F, Performance Counter Counter Registers
      if (csr_addr[11:5] == 7'b0111100) begin
        is_pccr     = 1'b1;

        pccr_index = csr_addr[4:0];
`ifdef  ASIC_SYNTHESIS
        perf_rdata = PCCR_q[0];
`else
        perf_rdata = csr_addr[4:0] < N_PERF_COUNTERS ? PCCR_q[csr_addr[4:0]] : '0;
`endif
      end
    end
  end


  // performance counter counter update logic
`ifdef ASIC_SYNTHESIS
  // for synthesis we just have one performance counter register
  assign PCCR_inc[0] = (|(PCCR_in & PCER_q)) & PCMR_q[0];

  always_comb begin
    PCCR_n[0]   = PCCR_q[0];

    if ((PCCR_inc_q[0] == 1'b1) && ((PCCR_q[0] != 32'hFFFFFFFF) || (PCMR_q[1] == 1'b0))) begin
      PCCR_n[0] = PCCR_q[0] + 32'h1;
    end

    if (is_pccr) begin
      unique case (csr_op_i)
        CSR_OP_NONE:   ;
        CSR_OP_WRITE:  PCCR_n[0] =  csr_wdata_i;
        CSR_OP_SET:    PCCR_n[0] =  csr_wdata_i | PCCR_q[0];
        CSR_OP_CLEAR:  PCCR_n[0] = ~csr_wdata_i & PCCR_q[0];
        default:       PCCR_n[0] = 'X;
      endcase
    end
  end
`else
  always_comb begin
    for (int c = 0; c < N_PERF_COUNTERS; c++) begin : perf_counters_inc
      PCCR_inc[c] = PCCR_in[c] & PCER_q[c] & PCMR_q[0];

      PCCR_n[c]   = PCCR_q[c];

      if ((PCCR_inc_q[c] == 1'b1) && ((PCCR_q[c] != 32'hFFFFFFFF) || (PCMR_q[1] == 1'b0))) begin
        PCCR_n[c] = PCCR_q[c] + 32'h1;
      end

      if (is_pccr && (pccr_all_sel || pccr_index == c)) begin
        unique case (csr_op_i)
          CSR_OP_NONE:   ;
          CSR_OP_WRITE:  PCCR_n[c] =  csr_wdata_i;
          CSR_OP_SET:    PCCR_n[c] =  csr_wdata_i | PCCR_q[c];
          CSR_OP_CLEAR:  PCCR_n[c] = ~csr_wdata_i & PCCR_q[c];
          default:       PCCR_n[c] = 'X;
        endcase
      end
    end
  end
`endif

  // update PCMR and PCER
  always_comb begin
    PCMR_n = PCMR_q;
    PCER_n = PCER_q;

    if (is_pcmr) begin
      unique case (csr_op_i)
        CSR_OP_NONE:   ;
        CSR_OP_WRITE:  PCMR_n =  csr_wdata_i[1:0];
        CSR_OP_SET:    PCMR_n =  csr_wdata_i[1:0] | PCMR_q;
        CSR_OP_CLEAR:  PCMR_n = ~csr_wdata_i[1:0] & PCMR_q;
        default:       PCMR_n = 'X;
      endcase
    end

    if (is_pcer) begin
      unique case (csr_op_i)
        CSR_OP_NONE:   ;
        CSR_OP_WRITE:  PCER_n =  csr_wdata_i[N_PERF_COUNTERS-1:0];
        CSR_OP_SET:    PCER_n =  csr_wdata_i[N_PERF_COUNTERS-1:0] | PCER_q;
        CSR_OP_CLEAR:  PCER_n = ~csr_wdata_i[N_PERF_COUNTERS-1:0] & PCER_q;
        default:       PCER_n = 'X;
      endcase
    end
  end

  // Performance Counter Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      PCER_q <= '0;
      PCMR_q <= 2'h3;

      for (int r = 0; r < N_PERF_REGS; r++) begin
        PCCR_q[r]     <= '0;
        PCCR_inc_q[r] <= '0;
      end
    end else begin
      PCER_q <= PCER_n;
      PCMR_q <= PCMR_n;

      for (int r = 0; r < N_PERF_REGS; r++) begin
        PCCR_q[r]     <= PCCR_n[r];
        PCCR_inc_q[r] <= PCCR_inc[r];
      end
    end
  end

endmodule
