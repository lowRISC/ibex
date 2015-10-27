////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Florian Glaser - glaserf@ethz.ch                           //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
//                                                                            //
// Create Date:    11/07/2014                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    debug_unit.sv                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Debug controller                                           //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (December 1, 2014) Merge with current OR10N core,          //
//                 changed port and signal names                              //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "defines.sv"

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
  output logic        dbg_st_en_o,     // Single-step trace mode enabled
  output logic [1:0]  dbg_dsr_o,       // debug stop register

  output logic        stall_core_o,
  output logic        flush_pipe_o,
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

  input  logic  [1:0] jump_in_ex_i,
  input  logic        branch_taken_i,

  output logic [31:0] npc_o,
  output logic        set_npc_o
);


  // registers for debug control
  logic [1:0] DSR_DP,  DSR_DN;  // Debug Stop Register: IIE, INTE
  logic [1:0] DMR1_DP, DMR1_DN; // only single step trace and branch trace bits

  // BP control FSM
  enum logic [2:0] {Idle, Trap, DebugStall, StallCore} BP_State_SN, BP_State_SP;

  // ppc/npc tracking
  enum logic [1:0] {IFID, IFEX, IDEX} pc_tracking_fsm_cs, pc_tracking_fsm_ns;
  logic [31:0] ppc_int, npc_int;

  // ack to debug interface
  assign dbginf_ack_o = dbginf_strobe_i && ((BP_State_SP == StallCore) || (dbginf_addr_i[15:11] == 5'b00110));


  always_comb
  begin
    BP_State_SN  = BP_State_SP;
    stall_core_o = 1'b0;
    dbginf_bp_o  = 1'b0;
    flush_pipe_o = 1'b0;

    case (BP_State_SP)
      Idle:
      begin
        if(trap_i == 1'b1)
        begin
          dbginf_bp_o  = 1'b1;
          stall_core_o = 1'b1;
          BP_State_SN  = StallCore;
        end
        else if(dbginf_stall_i)
        begin
          flush_pipe_o = 1'b1;
          BP_State_SN  = DebugStall;
        end
      end

      // A stall from adv dbg unit was seen, flush the pipeline and wait for unstalling
      DebugStall:
      begin
        flush_pipe_o = 1'b1;

        if(trap_i == 1'b1)
        begin
          stall_core_o = 1'b1;
          BP_State_SN  = StallCore;
        end
      end

      StallCore:
      begin
        stall_core_o = 1'b1;

        if(~dbginf_stall_i)
          BP_State_SN = Idle;
      end

      default: BP_State_SN = Idle;
    endcase // case (BP_State_SP)
  end


  // data to GPRs and SPRs
  assign regfile_wdata_o   = dbginf_data_i;

  assign dbg_st_en_o       = DMR1_DP[0];
  assign dbg_dsr_o         = DSR_DP;

  assign npc_o     = dbginf_data_i;


  // address decoding, write and read controller
  always_comb
  begin
    DMR1_DN            = DMR1_DP;
    DSR_DN             = DSR_DP;
    dbginf_data_o      = 32'b0;
    regfile_we_o       = 1'b0;
    regfile_addr_o     = 'h0;
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
              DMR1_DN = dbginf_data_i[`DMR1_ST+1:`DMR1_ST];
            else
              dbginf_data_o[`DMR1_ST+1:`DMR1_ST] = DMR1_DP;
          end
          11'd20: begin // SP_DSR
            // currently we only handle IIE and INTE
            if(dbginf_we_i == 1'b1)
              DSR_DN = dbginf_data_i[7:6];
            else
              dbginf_data_o[7:6] = DSR_DP[1:0];
          end
          default: ;
        endcase // casex [10:0]
      end
      // check if internal registers (GPR or SPR) are accessed
      else if(BP_State_SP == StallCore)
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
    if (stall_core_o && (BP_State_SP != StallCore)) begin
      pc_tracking_fsm_ns = IFID;

      if (jump_in_ex_i == `BRANCH_COND) begin
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
      DMR1_DP            <= 2'b0;
      DSR_DP             <= 'b0;
      BP_State_SP        <= Idle;
      pc_tracking_fsm_cs <= IFID;
    end
    else begin
      DMR1_DP            <= DMR1_DN;
      DSR_DP             <= DSR_DN;
      BP_State_SP        <= BP_State_SN;
      pc_tracking_fsm_cs <= pc_tracking_fsm_ns;
    end
  end

endmodule // debug_unit
