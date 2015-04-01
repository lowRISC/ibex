////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Florian Glaser - glaserf@ethz.ch                           //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
//                                                                            //
// Create Date:    11/07/2014                                                 //
// Design Name:    Pipelined OpenRISC Processor                               //
// Module Name:    debug_unit.sv                                              //
// Project Name:   OR10N                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Debug Controller for the pipelined processor               //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (December 1, 2014) Merge with current OR10N core,          //
//                 changed port and signal names                              //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "defines.sv"

module debug_unit
(
  input logic          clk,
  input logic          rst_n,

  // signals to Debug Interface
  input  logic         dbginf_stall_i,
  output logic         dbginf_bp_o,
  input  logic         dbginf_strobe_i,
  output logic         dbginf_ack_o,
  input  logic         dbginf_we_i,
  input  logic [15:0]  dbginf_addr_i,
  input  logic [31:0]  dbginf_data_i,
  output logic [31:0]  dbginf_data_o,

  // signals to core
  output logic         dbg_st_en_o,     // Single-step trace mode enabled
  output logic [1:0]   dbg_dsr_o,       // debug stop register

  output logic         stall_core_o,
  output logic         flush_pipe_o,
  input  logic         pipe_flushed_i,
  input  logic         trap_i,

  output logic         sp_mux_o,
  output logic         regfile_mux_o,
  output logic         regfile_we_o,
  output logic [15:0]  regfile_addr_o,
  output logic [31:0]  regfile_wdata_o,
  input  logic [31:0]  regfile_rdata_i

  );

  // registers for debug control
  logic [1:0]         DSR_DP,  DSR_DN;  // Debug Stop Register: IIE, INTE
  logic [1:0]         DMR1_DP, DMR1_DN; // only single step trace and branch trace bits
  logic [2*`N_WP-1:0] DMR2_DP, DMR2_DN; // only BP enable control and BP cause status

  // watchpoint status
  logic [`N_WP-1:0]   WP_Status_D;

  // BP control FSM
  enum logic [2:0]   {Idle, Trap, DebugStall, StallCore} BP_State_SN, BP_State_SP;

  // ack to debug interface
  assign dbginf_ack_o = (dbginf_strobe_i && (BP_State_SP == StallCore));

  always_comb
  begin
    BP_State_SN   = BP_State_SP;
    stall_core_o  = 1'b0;
    dbginf_bp_o   = 1'b0;
    flush_pipe_o  = 1'b0;
    case (BP_State_SP)
      Idle:
      begin
        if(trap_i == 1'b1)
          BP_State_SN = Trap;

        if(dbginf_stall_i)
        begin
          flush_pipe_o = 1'b1;
          BP_State_SN = DebugStall;
        end
      end

      // A trap was encountered, wait for for the pipeline to be
      // flushed
      Trap:
      begin
        if(pipe_flushed_i == 1'b1)
        begin
          dbginf_bp_o = 1'b1;
          BP_State_SN = StallCore;
        end
      end

      // A stall from adv dbg was seen, flush the pipeline and wait for unstalling
      DebugStall:
      begin
        flush_pipe_o = 1'b1;

        if(pipe_flushed_i == 1'b1)
        begin
          BP_State_SN = StallCore;
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

  // address decoding, write and read controller
  always_comb
  begin
    DMR1_DN            = DMR1_DP;
    DMR2_DN[`N_WP-1:0] = DMR2_DP[`N_WP-1:0];
    DSR_DN             = DSR_DP;
    dbginf_data_o      = 32'b0;
    regfile_we_o       = 1'b0;
    regfile_addr_o     = 16'b0;
    regfile_mux_o      = 1'b0;
    sp_mux_o           = 1'b0;

    if(dbginf_strobe_i == 1'b1) begin
      // address decoding, first stage: evaluate higher 5 Bits to detect if debug regs are accessed
      if(dbginf_addr_i[15:11] == 5'b00110) begin
        // second stage: evaluate Bits 10:0 to detect which part of debug registers is accessed
        casex(dbginf_addr_i[10:0])
          11'd16: begin // SP_DMR1
            if(dbginf_we_i == 1'b1)
              DMR1_DN = dbginf_data_i[`DMR1_ST+1:`DMR1_ST];
            else
              dbginf_data_o[`DMR1_ST+1:`DMR1_ST] = DMR1_DP;
          end
          11'd17: begin // SP_DMR2
            if(dbginf_we_i == 1'b1)
              DMR2_DN[`N_WP-1:0] = dbginf_data_i[`DMR2_WGB0 + (`N_WP-1):`DMR2_WGB0];
            else
              dbginf_data_o[`DMR2_WGB0 + (`N_WP-1):`DMR2_WGB0] = DMR2_DP[`N_WP-1:0];
              dbginf_data_o[`DMR2_WBS0 + (`N_WP-1):`DMR2_WBS0] = DMR2_DP[2*`N_WP-1:`N_WP];
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
      // check if GPRs are accessed
      else if(dbginf_addr_i[15:10] == 6'b000001)
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
        sp_mux_o        = 1'b1;
        regfile_addr_o  = dbginf_addr_i;

        if(dbginf_we_i == 1'b1)
          regfile_we_o = 1'b1;
        else
          dbginf_data_o = regfile_rdata_i;
      end
    end
  end

  // normal FF setup
  always_ff@(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      DMR1_DP     <= 2'b0;
      DMR2_DP     <= 'b0;
      DSR_DP      <= 'b0;
      BP_State_SP <= Idle;
    end
    else begin
      DMR1_DP     <= DMR1_DN;
      DMR2_DP     <= DMR2_DN;
      DSR_DP      <= DSR_DN;
      BP_State_SP <= BP_State_SN;
    end
  end // always_ff@ (posedge clk or negedge rst_n)

endmodule // debug_unit
