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
// Description:    Control and Status Registers (CSRs) following the RISC-V   //
//                 Privileged Specification, draft version 1.11               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

/**
 * Control and Status Registers
 *
 * Control and Status Registers (CSRs) following the RISC-V Privileged
 * Specification, draft version 1.11
 */
module ibex_cs_registers #(
    parameter int unsigned MHPMCounterNum   = 8,
    parameter int unsigned MHPMCounterWidth = 40,
    parameter bit RV32E                     = 0,
    parameter bit RV32M                     = 0
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

    output logic                      illegal_csr_insn_o, // access to non-existent CSR,
                                                          // with wrong priviledge level, or
                                                          // missing write permissions
    // Performance Counters
    input  logic                      insn_ret_i,         // instr retired in ID/EX stage
    input  logic                      id_valid_i,         // ID stage is done
    input  logic                      is_compressed_i,    // compressed instr in ID
    input  logic                      is_decoding_i,      // controller is in DECODE state

    input  logic                      imiss_i,            // instr fetch
    input  logic                      pc_set_i,           // PC was set to a new value
    input  logic                      jump_i,             // jump instr seen (j, jr, jal, jalr)
    input  logic                      branch_i,           // branch instr seen (bf, bnf)
    input  logic                      branch_taken_i,     // branch was taken
    input  logic                      mem_load_i,         // load from memory in this cycle
    input  logic                      mem_store_i,        // store to memory in this cycle
    input  logic                      lsu_busy_i
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

  // Hardware performance monitor signals
  logic [31:0] mcountinhibit_n, mcountinhibit_q, mcountinhibit;
  logic [31:0] mcountinhibit_force;
  logic        mcountinhibit_we;
  logic [63:0] mhpmcounter_mask [32];
  logic [63:0] mhpmcounter_n [32];
  logic [63:0] mhpmcounter_q [32];
  logic [31:0] mhpmcounter_we;
  logic [31:0] mhpmcounterh_we;
  logic [31:0] mhpmcounter_incr;
  logic [31:0] mhpmevent [32];
  logic  [4:0] mhpmcounter_idx;

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
  Status_t     mstatus_q, mstatus_n;
  logic [31:0] exception_pc;

  // Access violation signals
  logic        illegal_csr;
  logic        illegal_csr_priv;
  logic        illegal_csr_write;

  /////////////
  // CSR reg //
  /////////////

  logic [$bits(csr_num_e)-1:0] csr_addr;
  assign csr_addr           = {csr_addr_i};
  assign mhpmcounter_idx    = csr_addr[4:0];

  assign illegal_csr_priv   = 1'b0; // we only support M-mode
  assign illegal_csr_write  = (csr_addr[11:10] == 2'b11) && csr_we_int;
  assign illegal_csr_insn_o = illegal_csr | illegal_csr_write | illegal_csr_priv;

  // read logic
  always_comb begin
    csr_rdata_int = '0;
    illegal_csr   = 1'b0;

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

      CSR_DCSR:      csr_rdata_int = dcsr_q;
      CSR_DPC:       csr_rdata_int = depc_q;
      CSR_DSCRATCH0: csr_rdata_int = dscratch0_q;
      CSR_DSCRATCH1: csr_rdata_int = dscratch1_q;

      // Machine Counter/Timers
      CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit;
      CSR_MCYCLE:        csr_rdata_int = mhpmcounter_q[0][31: 0];
      CSR_MCYCLEH:       csr_rdata_int = mhpmcounter_q[0][63:32];
      CSR_MINSTRET:      csr_rdata_int = mhpmcounter_q[2][31: 0];
      CSR_MINSTRETH:     csr_rdata_int = mhpmcounter_q[2][63:32];

      default: begin
        if (csr_addr_i == CSR_MCOUNTER_SETUP_MASK) begin
          csr_rdata_int = mhpmevent[mhpmcounter_idx];
          // check access to non-existent or already covered CSRs
          if ((csr_addr[4:0] == 5'b00000) ||     // CSR_MCOUNTINHIBIT
              (csr_addr[4:0] == 5'b00001) ||
              (csr_addr[4:0] == 5'b00010)) begin
            illegal_csr = csr_access_i;
          end

        end else if (csr_addr_i == CSR_MCOUNTER_MASK) begin
          csr_rdata_int = mhpmcounter_q[mhpmcounter_idx][31: 0];
          // check access to non-existent or already covered CSRs
          if ((csr_addr[4:0] == 5'b00000) ||     // CSR_MCYCLE
              (csr_addr[4:0] == 5'b00001) ||
              (csr_addr[4:0] == 5'b00010)) begin // CSR_MINSTRET
            illegal_csr = csr_access_i;
          end

        end else if (csr_addr_i == CSR_MCOUNTERH_MASK) begin
          csr_rdata_int = mhpmcounter_q[mhpmcounter_idx][63:32];
          // check access to non-existent or already covered CSRs
          if ((csr_addr[4:0] == 5'b00000) ||     // CSR_MCYCLEH
              (csr_addr[4:0] == 5'b00001) ||
              (csr_addr[4:0] == 5'b00010)) begin // CSR_MINSTRETH
            illegal_csr = csr_access_i;
          end
        end else begin
          illegal_csr = csr_access_i;
        end
      end
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

    mcountinhibit_we = 1'b0;
    mhpmcounter_we   = '0;
    mhpmcounterh_we  = '0;

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

      CSR_MCOUNTINHIBIT: begin
        if (csr_we_int) begin
          mcountinhibit_we = 1'b1;
        end
      end

      CSR_MCYCLE: begin
        if (csr_we_int) begin
          mhpmcounter_we[0] = 1'b1;
        end
      end

      CSR_MCYCLEH: begin
        if (csr_we_int) begin
          mhpmcounterh_we[0] = 1'b1;
        end
      end

      CSR_MINSTRET: begin
        if (csr_we_int) begin
          mhpmcounter_we[2] = 1'b1;
        end
      end

      CSR_MINSTRETH: begin
        if (csr_we_int) begin
          mhpmcounterh_we[2] = 1'b1;
        end
      end

      default: begin
        if (csr_we_int == 1'b1) begin
          // performance counters and event selector
          if (csr_addr_i == CSR_MCOUNTER_MASK) begin
            mhpmcounter_we[mhpmcounter_idx] = 1'b1;
          end else if (csr_addr_i == CSR_MCOUNTERH_MASK) begin
            mhpmcounterh_we[mhpmcounter_idx] = 1'b1;
          end
        end
      end
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
      CSR_OP_READ: begin
        csr_wdata_int = csr_wdata_i;
        csr_we_int    = 1'b0;
      end
      default: begin
        csr_wdata_int = 'X;
        csr_we_int    = 1'bX;
      end
    endcase
  end

  assign csr_rdata_o = csr_rdata_int;

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
  //  Performance monitor //
  //////////////////////////

  // update enable signals
  always_comb begin : mcountinhibit_update
    if (mcountinhibit_we == 1'b1) begin
      mcountinhibit_n = csr_wdata_int;
    end else begin
      mcountinhibit_n = mcountinhibit_q;
    end
    // bit 1 must always be 0
    mcountinhibit_n[1] = 1'b0;
  end

  assign mcountinhibit_force = {{29-MHPMCounterNum{1'b1}}, {MHPMCounterNum{1'b0}}, 3'b000};
  assign mcountinhibit       = mcountinhibit_q | mcountinhibit_force;

  // event selection (hardwired) & control
  assign mhpmcounter_incr[0]  = 1'b1;                // mcycle
  assign mhpmcounter_incr[1]  = 1'b0;                // reserved
  assign mhpmcounter_incr[2]  = insn_ret_i;          // minstret
  assign mhpmcounter_incr[3]  = lsu_busy_i;          // cycles waiting for data memory
  assign mhpmcounter_incr[4]  = imiss_i & ~pc_set_i; // cycles waiting for instr fetches ex.
                                                     // jumps and branches
  assign mhpmcounter_incr[5]  = mem_load_i;          // num of loads
  assign mhpmcounter_incr[6]  = mem_store_i;         // num of stores
  assign mhpmcounter_incr[7]  = jump_i;              // num of jumps (unconditional)
  assign mhpmcounter_incr[8]  = branch_i;            // num of branches (conditional)
  assign mhpmcounter_incr[9]  = branch_taken_i;      // num of taken branches (conditional)
  assign mhpmcounter_incr[10] = is_compressed_i      // num of compressed instr
      & id_valid_i & is_decoding_i;

  for (genvar i=3+MHPMCounterNum; i<32; i++) begin : gen_mhpmcounter_incr_inactive
    assign mhpmcounter_incr[i] = 1'b0;
  end

  // event selector (hardwired, 0 means no event)
  always_comb begin : gen_mhpmevent

    // activate all
    for (int i=0; i<32; i++) begin : gen_mhpmevent_active
      mhpmevent[i][i] = 1'b1;
    end

    // deactivate
    mhpmevent[1] = '0; // not existing, reserved
    for (int i=3+MHPMCounterNum; i<32; i++) begin : gen_mhpmevent_inactive
      mhpmevent[i] = '0;
    end
  end

  // mask, controls effective counter width
  always_comb begin : gen_mask

    for (int i=0; i<3; i++) begin : gen_mask_fixed
      // mcycle, mtime, minstret are always 64 bit wide
      mhpmcounter_mask[i] = {64{1'b1}};
    end

    for (int i=3; i<32; i++) begin : gen_mask_configurable
      // mhpmcounters have a configurable width
      mhpmcounter_mask[i] = {{{64-MHPMCounterWidth}{1'b0}}, {MHPMCounterWidth{1'b1}}};
    end
  end

  // update
  always_comb begin : mhpmcounter_update
    mhpmcounter_n = mhpmcounter_q;

    for (int i=0; i<32; i++) begin : gen_mhpmcounter_update

      // increment
      if (mhpmcounter_incr[i] & ~mcountinhibit[i]) begin
        mhpmcounter_n[i] = mhpmcounter_mask[i] & (mhpmcounter_n[i] + 64'h1);
      end

      // write
      if (mhpmcounter_we[i]) begin
        mhpmcounter_n[i][31: 0] = mhpmcounter_mask[i][31: 0] & csr_wdata_int;
      end else if (mhpmcounterh_we[i]) begin
        mhpmcounter_n[i][63:32] = mhpmcounter_mask[i][63:32] & csr_wdata_int;
      end
    end
  end

  // performance monitor registers
  always_ff @(posedge clk_i or negedge rst_ni) begin : perf_counter_registers
    if (!rst_ni) begin
      mcountinhibit_q    <= '0;
      for (int i=0; i<32; i++) begin
        mhpmcounter_q[i] <= '0;
      end
    end else begin
      mhpmcounter_q      <= mhpmcounter_n;
      mcountinhibit_q    <= mcountinhibit_n;
    end
  end

endmodule
