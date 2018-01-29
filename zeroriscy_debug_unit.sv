// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Debug Unit                                                 //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Debug controller                                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "zeroriscy_config.sv"

import zeroriscy_defines::*;

module zeroriscy_debug_unit
#(
    parameter REG_ADDR_WIDTH      = 5
)
(
  input logic         clk,
  input logic         rst_n,

  // Debug Interface
  input  logic        debug_req_i,
  output logic        debug_gnt_o,
  output logic        debug_rvalid_o,
  input  logic [14:0] debug_addr_i,
  input  logic        debug_we_i,
  input  logic [31:0] debug_wdata_i,
  output logic [31:0] debug_rdata_o,

  output logic        debug_halted_o,
  input  logic        debug_halt_i,
  input  logic        debug_resume_i,

  // signals to core
  output logic [DBG_SETS_W-1:0] settings_o,

  input  logic        trap_i,      // trap found, need to stop the core now
  input  logic [5:0]  exc_cause_i, // if it was a trap, then the exception controller knows more
  output logic        stall_o,     // after we got control, we control the stall signal
  output logic        dbg_req_o,
  input  logic        dbg_ack_i,

  // register file read port
  output logic        regfile_rreq_o,
  output logic [(REG_ADDR_WIDTH-1):0] regfile_raddr_o,
  input  logic [31:0] regfile_rdata_i,

  // register file write port
  output logic        regfile_wreq_o,
  output logic [(REG_ADDR_WIDTH-1):0] regfile_waddr_o,
  output logic [31:0] regfile_wdata_o,

  // CSR read/write port
  output logic        csr_req_o,
  output logic [11:0] csr_addr_o,
  output logic        csr_we_o,
  output logic [31:0] csr_wdata_o,
  input  logic [31:0] csr_rdata_i,

  // Signals for PPC & NPC register
  input  logic [31:0] pc_if_i,
  input  logic [31:0] pc_id_i,

  input  logic        instr_valid_id_i,

  input  logic        sleeping_i,

  output logic        jump_req_o,
  output logic [31:0] jump_addr_o
);

  enum logic [2:0] {RD_NONE, RD_CSR, RD_GPR, RD_DBGA, RD_DBGS} rdata_sel_q, rdata_sel_n;

  enum logic [0:0] {FIRST, SECOND} state_q, state_n;

  logic [DBG_SETS_W-1:0] settings_q, settings_n;

  // for timing critical register file access we need to keep those in FFs
  logic [14:0] addr_q;
  logic [31:0] wdata_q; // mainly for jumps
  logic        regfile_rreq_q, regfile_rreq_n;
  logic        jump_req_q, jump_req_n;

  // not timing critical
  logic        csr_req_q, csr_req_n;
  logic        regfile_wreq;


  enum logic [1:0] {RUNNING, HALT_REQ, HALT} stall_cs, stall_ns;
  logic [31:0] dbg_rdata;
  logic        dbg_resume;
  logic        dbg_halt;
  logic [5:0]  dbg_cause_q, dbg_cause_n;
  logic        dbg_ssth_q,  dbg_ssth_n;

  logic        ssth_clear;


  // ppc/npc tracking
  logic [31:0] ppc_int, npc_int;


  // address decoding, write and read controller
  always_comb
  begin
    rdata_sel_n    = RD_NONE;
    state_n        = FIRST;

    debug_gnt_o    = 1'b0;

    regfile_rreq_n = 1'b0;
    regfile_wreq   = 1'b0;
    csr_req_n      = 1'b0;
    csr_we_o       = 1'b0;
    jump_req_n     = 1'b0;

    dbg_resume     = 1'b0;
    dbg_halt       = 1'b0;
    settings_n     = settings_q;

    ssth_clear     = 1'b0;

    if (debug_req_i) begin
      if (debug_we_i) begin
        //----------------------------------------------------------------------------
        // write access
        //----------------------------------------------------------------------------
        if (debug_addr_i[14]) begin
          // CSR access
          if (state_q == FIRST) begin
            // only grant in second cycle, address and data have been latched by then
            debug_gnt_o = 1'b0;
            state_n     = SECOND;

            if (debug_halted_o) begin
              // access to internal registers are only allowed when the core is halted
              csr_req_n = 1'b1;
            end
          end else begin
            debug_gnt_o = 1'b1; // grant it even when invalid access to not block
            state_n     = FIRST;
            csr_we_o    = 1'b1;
          end
        end else begin
          // non-CSR access
          unique case (debug_addr_i[13:8])
            6'b00_0000: begin // Debug Registers, always accessible
              debug_gnt_o = 1'b1;

              unique case (debug_addr_i[6:2])
                5'b0_0000: begin // DBG_CTRL
                  if (debug_wdata_i[16]) begin
                    // HALT set
                    if (~debug_halted_o) begin
                      // not halt, so STOP
                      dbg_halt = 1'b1;
                    end
                  end else begin
                    // RESUME set
                    if (debug_halted_o) begin
                      dbg_resume = 1'b1;
                    end
                  end

                  settings_n[DBG_SETS_SSTE] = debug_wdata_i[0];
                end
                5'b0_0001: begin // DBG_HIT
                  ssth_clear = debug_wdata_i[0];
                end
                5'b0_0010: begin // DBG_IE
                  settings_n[DBG_SETS_ECALL] = debug_wdata_i[11];
                  settings_n[DBG_SETS_ELSU]  = debug_wdata_i[7] | debug_wdata_i[5];
                  settings_n[DBG_SETS_EBRK]  = debug_wdata_i[3];
                  settings_n[DBG_SETS_EILL]  = debug_wdata_i[2];
                end
                default:;
              endcase
            end

            6'b10_0000: begin // Debug Registers, only accessible when in debug
              debug_gnt_o = 1'b1; // grant it even when invalid access to not block

              if (debug_halted_o) begin
                unique case (debug_addr_i[6:2])
                  5'b0_0000: jump_req_n = 1'b1; // DNPC
                  default:;
                endcase
              end
            end

            6'b00_0100: begin // General-Purpose Registers
              debug_gnt_o = 1'b1; // grant it even when invalid access to not block

              if (debug_halted_o) begin
                regfile_wreq = 1'b1;
              end
            end

            default: debug_gnt_o = 1'b1; // grant it even when invalid access to not block
          endcase
        end
      end else begin
        //----------------------------------------------------------------------------
        // read access
        //----------------------------------------------------------------------------
        if (debug_addr_i[14]) begin
          debug_gnt_o = 1'b1; // grant it even when invalid access to not block

          // CSR access
          if (debug_halted_o) begin
            // access to internal registers are only allowed when the core is halted
            csr_req_n   = 1'b1;
            rdata_sel_n = RD_CSR;
          end
        end else begin
          // non-CSR access
          unique case (debug_addr_i[13:8])
            6'b00_0000: begin // Debug Registers, always accessible
              debug_gnt_o = 1'b1;

              rdata_sel_n = RD_DBGA;
            end

            6'b10_0000: begin // Debug Registers, only accessible when in debug
              debug_gnt_o = 1'b1; // grant it even when invalid access to not block

              rdata_sel_n = RD_DBGS;
            end

            6'b00_0100: begin // General-Purpose Registers
              debug_gnt_o = 1'b1; // grant it even when invalid access to not block

              if (debug_halted_o) begin
                regfile_rreq_n = 1'b1;
                rdata_sel_n    = RD_GPR;
              end
            end

            default: debug_gnt_o = 1'b1; // grant it even when invalid access to not block
          endcase
        end
      end
    end
  end

  //----------------------------------------------------------------------------
  // debug register read access
  //
  // Since those are combinational, we can do it in the cycle where we set
  // rvalid. The address has been latched into addr_q
  //----------------------------------------------------------------------------
  always_comb
  begin
    dbg_rdata = '0;

    case (rdata_sel_q)
      RD_DBGA: begin
        unique case (addr_q[6:2])
          5'h00: dbg_rdata[31:0] = {15'b0, debug_halted_o, 15'b0, settings_q[DBG_SETS_SSTE]}; // DBG_CTRL
          5'h01: dbg_rdata[31:0] = {15'b0, sleeping_i, 15'b0, dbg_ssth_q}; // DBG_HIT
          5'h02: begin // DBG_IE
            dbg_rdata[31:16] = '0;
            dbg_rdata[15:12] = '0;
            dbg_rdata[11]    = settings_q[DBG_SETS_ECALL];
            dbg_rdata[10: 8] = '0;
            dbg_rdata[ 7]    = settings_q[DBG_SETS_ELSU];
            dbg_rdata[ 6]    = 1'b0;
            dbg_rdata[ 5]    = settings_q[DBG_SETS_ELSU];
            dbg_rdata[ 4]    = 1'b0;
            dbg_rdata[ 3]    = settings_q[DBG_SETS_EBRK];
            dbg_rdata[ 2]    = settings_q[DBG_SETS_EILL];
            dbg_rdata[ 1: 0] = '0;
          end
          5'h03: dbg_rdata = {dbg_cause_q[5], 26'b0, dbg_cause_q[4:0]}; // DBG_CAUSE
          5'h10: dbg_rdata = '0; // DBG_BPCTRL0
          5'h12: dbg_rdata = '0; // DBG_BPCTRL1
          5'h14: dbg_rdata = '0; // DBG_BPCTRL2
          5'h16: dbg_rdata = '0; // DBG_BPCTRL3
          5'h18: dbg_rdata = '0; // DBG_BPCTRL4
          5'h1A: dbg_rdata = '0; // DBG_BPCTRL5
          5'h1C: dbg_rdata = '0; // DBG_BPCTRL6
          5'h1E: dbg_rdata = '0; // DBG_BPCTRL7
          default:;
        endcase
      end

      RD_DBGS: begin
        unique case (addr_q[2:2])
          1'b0: dbg_rdata = npc_int; // DBG_NPC
          1'b1: dbg_rdata = ppc_int; // DBG_PPC
          default:;
        endcase
      end

      default:;
    endcase
  end

  //----------------------------------------------------------------------------
  // read data mux
  //----------------------------------------------------------------------------
  always_comb
  begin
    debug_rdata_o = '0;

    case (rdata_sel_q)
      RD_CSR:  debug_rdata_o = csr_rdata_i;
      RD_GPR:  debug_rdata_o = regfile_rdata_i;
      RD_DBGA: debug_rdata_o = dbg_rdata;
      RD_DBGS: debug_rdata_o = dbg_rdata;
		default: ;
    endcase
  end

  //----------------------------------------------------------------------------
  // rvalid generation
  //----------------------------------------------------------------------------
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (~rst_n) begin
      debug_rvalid_o <= 1'b0;
    end else begin
      debug_rvalid_o <= debug_gnt_o; // always give the rvalid one cycle after gnt
    end
  end

  //----------------------------------------------------------------------------
  // stall control
  //----------------------------------------------------------------------------
  always_comb
  begin
    stall_ns       = stall_cs;
    dbg_req_o      = 1'b0;
    stall_o        = 1'b0;
    debug_halted_o = 1'b0;
    dbg_cause_n    = dbg_cause_q;
    dbg_ssth_n     = dbg_ssth_q;

    case (stall_cs)
      RUNNING: begin
        dbg_ssth_n = 1'b0;

        if (dbg_halt | debug_halt_i | trap_i) begin
          dbg_req_o   = 1'b1;
          stall_ns    = HALT_REQ;

          if (trap_i) begin
            if (settings_q[DBG_SETS_SSTE])
              dbg_ssth_n = 1'b1;

            dbg_cause_n = exc_cause_i;
          end else begin
            dbg_cause_n = DBG_CAUSE_HALT;
          end
        end
      end

      HALT_REQ: begin
        dbg_req_o = 1'b1;

        if (dbg_ack_i)
          stall_ns = HALT;

        if (dbg_resume | debug_resume_i)
          stall_ns = RUNNING;
      end

      HALT: begin
        stall_o        = 1'b1;
        debug_halted_o = 1'b1;

        if (dbg_resume | debug_resume_i) begin
          stall_ns = RUNNING;
          stall_o  = 1'b0;
        end
      end
    endcase

    if (ssth_clear)
      dbg_ssth_n = 1'b0;
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (~rst_n) begin
      stall_cs    <= RUNNING;
      dbg_cause_q <= DBG_CAUSE_HALT;
      dbg_ssth_q  <= 1'b0;
    end else begin
      stall_cs    <= stall_ns;
      dbg_cause_q <= dbg_cause_n;
      dbg_ssth_q  <= dbg_ssth_n;
    end
  end

  //----------------------------------------------------------------------------
  // NPC/PPC selection
  //----------------------------------------------------------------------------

  assign ppc_int = pc_id_i;
  assign npc_int = pc_if_i;

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (~rst_n) begin

      addr_q             <= '0;
      wdata_q            <= '0;
      state_q            <= FIRST;
      rdata_sel_q        <= RD_NONE;
      regfile_rreq_q     <= 1'b0;
      csr_req_q          <= 1'b0;
      jump_req_q         <= 1'b0;

      settings_q         <= 1'b0;
    end else begin

      // settings
      settings_q         <= settings_n;

      // for the actual interface
      if (debug_req_i) begin
        addr_q  <= debug_addr_i;
        wdata_q <= debug_wdata_i;
        state_q <= state_n;
      end

      if (debug_req_i | debug_rvalid_o) begin
        // wait for either req or rvalid to set those FFs
        // This makes sure that they are only triggered once when there is
        // only one request, and the FFs can be properly clock gated otherwise
        regfile_rreq_q <= regfile_rreq_n;
        csr_req_q      <= csr_req_n;
        jump_req_q     <= jump_req_n;
        rdata_sel_q    <= rdata_sel_n;
      end
    end
  end

  assign regfile_rreq_o  = regfile_rreq_q;
  assign regfile_raddr_o = addr_q[6:2];

  assign regfile_wreq_o  = regfile_wreq;
  assign regfile_waddr_o = debug_addr_i[6:2];
  assign regfile_wdata_o = debug_wdata_i;

  assign csr_req_o       = csr_req_q;
  assign csr_addr_o      = addr_q[13:2];
  assign csr_wdata_o     = wdata_q;

  assign jump_req_o      = jump_req_q;
  assign jump_addr_o     = wdata_q;

  assign settings_o      = settings_q;

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
`ifndef VERILATOR
  // check that no registers are accessed when we are not in debug mode
  assert property (
    @(posedge clk) (debug_req_i) |-> ((debug_halted_o == 1'b1) ||
                                      ((debug_addr_i[14] != 1'b1) &&
                                       (debug_addr_i[13:7] != 5'b0_1001)  &&
                                       (debug_addr_i[13:7] != 5'b0_1000)) ) )
    else $warning("Trying to access internal debug registers while core is not stalled");

  // check that all accesses are word-aligned
  assert property (
    @(posedge clk) (debug_req_i) |-> (debug_addr_i[1:0] == 2'b00) );
`endif
endmodule // debug_unit
