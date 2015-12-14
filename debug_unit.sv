// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Florian Glaser - glaserf@ethz.ch                           //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Design Name:    Debug Unit                                                 //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Debug controller                                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "riscv_defines.sv"

module riscv_debug_unit
(
  input logic         clk,
  input logic         rst_n,

  // signals to Debug Interface
  input  logic        dbginf_stall_i,
  output logic        dbginf_bp_o,
  input  logic        dbginf_strobe_i,
  output logic        dbginf_ack_o,
  input  logic        dbginf_we_i,
  input  logic [15:0] dbginf_addr_i,
  input  logic [31:0] dbginf_data_i,
  output logic [31:0] dbginf_data_o,

  // signals to core
  output logic        dbg_step_en_o,   // Single-step trace mode enabled
  output logic [1:0]  dbg_dsr_o,       // debug stop register

  output logic        stall_core_o,
  output logic        stop_req_o,
  input  logic        trap_i,

  output logic        sp_mux_o,
  output logic        regfile_mux_o,
  output logic        regfile_we_o,
  output logic [11:0] regfile_addr_o,
  output logic [31:0] regfile_wdata_o,
  input  logic [31:0] regfile_rdata_i,

  // Signals for PPC & NPC register
  input  logic [31:0] curr_pc_if_i,
  input  logic [31:0] curr_pc_id_i,
  input  logic [31:0] branch_pc_i,

  input  logic        branch_in_ex_i,
  input  logic        branch_taken_i,

  output logic [31:0] npc_o,
  output logic        set_npc_o
);


  // registers for debug control
  logic [1:0] dsr_q,  dsr_n;  // Debug Stop Register: IIE, INTE
  logic [1:0] dmr1_q, dmr1_n; // only single step trace and branch trace bits

  // BP control FSM
  enum logic [1:0] {Idle, Trap, DebugStall, StallCore} bp_fsm_cs, bp_fsm_ns;

  // ppc/npc tracking
  enum logic [1:0] {IFID, IFEX, IDEX} pc_tracking_fsm_cs, pc_tracking_fsm_ns;
  logic [31:0] ppc_int, npc_int;

  // ack to debug interface
  assign dbginf_ack_o = dbginf_strobe_i && ((bp_fsm_cs == StallCore) || (dbginf_addr_i[15:11] == 5'b00110));


  always_comb
  begin
    bp_fsm_ns    = bp_fsm_cs;
    stall_core_o = 1'b0;
    dbginf_bp_o  = 1'b0;
    stop_req_o   = 1'b0;

    case (bp_fsm_cs)
      Idle:
      begin
        if(trap_i == 1'b1)
        begin
          dbginf_bp_o  = 1'b1;
          stall_core_o = 1'b1;
          bp_fsm_ns    = StallCore;
        end
        else if(dbginf_stall_i)
        begin
          stop_req_o   = 1'b1;
          bp_fsm_ns    = DebugStall;
        end
      end

      // A stall from adv dbg unit was seen, flush the pipeline and wait for unstalling
      DebugStall:
      begin
        stop_req_o   = 1'b1;

        if(trap_i == 1'b1)
        begin
          stall_core_o = 1'b1;
          bp_fsm_ns    = StallCore;
        end
      end

      StallCore:
      begin
        stall_core_o = 1'b1;

        if(~dbginf_stall_i)
          bp_fsm_ns = Idle;
      end

      default: bp_fsm_ns = Idle;
    endcase // case (bp_fsm_cs)
  end


  // data to GPRs and SPRs
  assign regfile_wdata_o   = dbginf_data_i;

  assign dbg_step_en_o     = dmr1_q[0];
  assign dbg_dsr_o         = dsr_q;

  assign npc_o             = dbginf_data_i;


  // address decoding, write and read controller
  always_comb
  begin
    dmr1_n             = dmr1_q;
    dsr_n              = dsr_q;
    dbginf_data_o      = 32'b0;
    regfile_we_o       = 1'b0;
    regfile_addr_o     = '0;
    regfile_mux_o      = 1'b0;
    sp_mux_o           = 1'b0;
    set_npc_o          = 1'b0;

    if(dbginf_strobe_i == 1'b1) begin
      // address decoding, first stage: evaluate higher 5 Bits to detect if debug regs are accessed
      if(dbginf_addr_i[15:11] == 5'b00110) begin
        // second stage: evaluate Bits 10:0 to detect which part of debug registers is accessed
        case (dbginf_addr_i[10:0])
          11'd0: begin // NPC
            set_npc_o = dbginf_we_i;

            dbginf_data_o = npc_int;
          end

          11'd1: begin // PPC
            dbginf_data_o = ppc_int;
          end

          11'd16: begin // SP_DMR1
            if(dbginf_we_i == 1'b1)
              dmr1_n = dbginf_data_i[`DMR1_ST+1:`DMR1_ST];
            else
              dbginf_data_o[`DMR1_ST+1:`DMR1_ST] = dmr1_q;
          end

          11'd20: begin // SP_DSR
            // currently we only handle IIE and INTE
            if(dbginf_we_i == 1'b1)
              dsr_n = dbginf_data_i[7:6];
            else
              dbginf_data_o[7:6] = dsr_q[1:0];
          end

          default: ;
        endcase
      end
      // check if internal registers (GPR or SPR) are accessed
      else if(bp_fsm_cs == StallCore)
      begin
        // check if GPRs are accessed
        if(dbginf_addr_i[15:10] == 6'b000001)
        begin
          regfile_mux_o       = 1'b1;
          regfile_addr_o[4:0] = dbginf_addr_i[4:0];

          if(dbginf_we_i == 1'b1)
            regfile_we_o  = 1'b1;
          else
            dbginf_data_o = regfile_rdata_i;
        end
        // some other SPR is accessed
        else
        begin
          sp_mux_o       = 1'b1;
          regfile_addr_o = dbginf_addr_i[11:0];

          if(dbginf_we_i == 1'b1)
            regfile_we_o = 1'b1;
          else
            dbginf_data_o = regfile_rdata_i;
        end
      end
    end
  end


  always_comb
  begin
    pc_tracking_fsm_ns = pc_tracking_fsm_cs;

    ppc_int = curr_pc_id_i;
    npc_int = curr_pc_if_i;

    // PPC/NPC mux
    unique case (pc_tracking_fsm_cs)
      IFID: begin
        ppc_int = curr_pc_id_i;
        npc_int = curr_pc_if_i;
      end

      IFEX: begin
        ppc_int = branch_pc_i;
        npc_int = curr_pc_if_i;
      end

      IDEX: begin
        ppc_int = branch_pc_i;
        npc_int = curr_pc_id_i;

        if (set_npc_o)
          pc_tracking_fsm_ns = IFEX;
      end

      default: begin
        pc_tracking_fsm_ns = IFID;
      end
    endcase

    // set state if trap is encountered
    if (stall_core_o && (bp_fsm_cs != StallCore)) begin
      pc_tracking_fsm_ns = IFID;

      if (branch_in_ex_i) begin
        if (branch_taken_i)
          pc_tracking_fsm_ns = IFEX;
        else
          pc_tracking_fsm_ns = IDEX;
      end
    end
  end


  always_ff@(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      dmr1_q             <= '0;
      dsr_q              <= '0;
      bp_fsm_cs          <= Idle;
      pc_tracking_fsm_cs <= IFID;
    end
    else begin
      dmr1_q             <= dmr1_n;
      dsr_q              <= dsr_n;
      bp_fsm_cs          <= bp_fsm_ns;
      pc_tracking_fsm_cs <= pc_tracking_fsm_ns;
    end
  end

endmodule // debug_unit
