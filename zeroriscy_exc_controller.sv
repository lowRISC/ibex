////////////////////////////////////////////////////////////////////////////////
// Copyright (C) 2017 ETH Zurich, University of Bologna                       //
// All rights reserved.                                                       //
//                                                                            //
// This code is under development and not yet released to the public.         //
// Until it is released, the code is under the copyright of ETH Zurich        //
// and the University of Bologna, and may contain unpublished work.           //
// Any reuse/redistribution should only be under explicit permission.         //
//                                                                            //
// Bug fixes and contributions will eventually be released under the          //
// SolderPad open hardware license and under the copyright of ETH Zurich      //
// and the University of Bologna.                                             //
//                                                                            //
// Engineer:       Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Exception Controller                                       //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Exception Controller of the pipelined processor            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import zeroriscy_defines::*;

module zeroriscy_exc_controller
(
  input  logic        clk,
  input  logic        rst_n,

  // handshake signals to controller
  output logic        int_req_o,
  output logic        ext_req_o,
  input  logic        ack_i,

  input  logic        ctr_decoding_i,

  output logic        trap_o,

  // to IF stage
  output logic  [1:0] pc_mux_o,       // selects target PC for exception

  // interrupt lines
  input  logic        irq_i,          // level-triggered interrupt inputs
  input  logic  [4:0] irq_id_i,       // interrupt id [0,1,....31]
  input  logic        irq_enable_i,   // interrupt enable bit from CSR

  // from decoder
  input  logic        ebrk_insn_i,    // ebrk instruction encountered (EBREAK)
  input  logic        illegal_insn_i, // illegal instruction encountered
  input  logic        ecall_insn_i,   // ecall instruction encountered

  // to CSR
  output logic [5:0]  cause_o,
  output logic        save_cause_o,

  // from debug unit
  input  logic [DBG_SETS_W-1:0] dbg_settings_i
);


  enum logic [1:0] { IDLE, WAIT_CONTROLLER_INT, WAIT_CONTROLLER_EXT, WAIT_CONTROLLER_DBG } exc_ctrl_cs, exc_ctrl_ns;

  logic int_req_int, ext_req_int;
  logic [1:0] pc_mux_int, pc_mux_int_q;
  logic [5:0] cause_int, cause_int_q;
  logic trap_int;

  // a trap towards the debug unit is generated when one of the
  // following conditions are true:
  // - ebreak instruction encountered
  // - single-stepping mode enabled
  // - illegal instruction exception and IIE bit is set
  // - IRQ and INTE bit is set and no exception is currently running
  // - Debuger requests halt
  assign trap_int =   (dbg_settings_i[DBG_SETS_SSTE])
                      | (ecall_insn_i            & dbg_settings_i[DBG_SETS_ECALL])
                      | (ebrk_insn_i             & dbg_settings_i[DBG_SETS_EBRK])
                      | (illegal_insn_i          & dbg_settings_i[DBG_SETS_EILL])
                      | (irq_enable_i & irq_i & dbg_settings_i[DBG_SETS_IRQ]);

  // request for exception/interrupt
  assign int_req_int =   ecall_insn_i
                     | illegal_insn_i;

  assign ext_req_int = irq_enable_i & irq_i;

  // Exception cause and ISR address selection
  always_comb
  begin
    cause_int  = 6'b0;
    pc_mux_int = '0;

    unique case(1'b1)

      ebrk_insn_i:
        cause_int  = 6'b0_00011;

      ecall_insn_i: begin
        cause_int  = 6'b0_01011;
        pc_mux_int = EXC_PC_ECALL;
      end

      illegal_insn_i: begin
        cause_int  = 6'b0_00010;
        pc_mux_int = EXC_PC_ILLINSN;
      end

      default: begin
        //exceptions have priority over interrupts
        if (irq_enable_i & irq_i) begin
          // pc_mux_int is a critical signal, so try to get it as soon as possible
          pc_mux_int = EXC_PC_IRQ;
          cause_int = {1'b1,irq_id_i};
        end
      end
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      cause_int_q  <= '0;
      pc_mux_int_q <= '0;
    end else if (exc_ctrl_cs == IDLE && (ctr_decoding_i | ext_req_o)) begin
      // save cause and ISR when new irq request is first sent to controller
      cause_int_q  <= cause_int;
      pc_mux_int_q <= pc_mux_int;
    end
  end


  // Exception cause and mux output (with bypass)
  assign cause_o      = cause_int_q;
  assign pc_mux_o     = pc_mux_int_q;

  // Exception controller FSM
  always_comb
  begin
    exc_ctrl_ns  = exc_ctrl_cs;
    int_req_o    = 1'b0;
    ext_req_o    = 1'b0;
    save_cause_o = 1'b0;
    trap_o       = 1'b0;

    unique case (exc_ctrl_cs)
      IDLE:
      begin
        int_req_o = int_req_int;
        ext_req_o = ext_req_int;
        trap_o    = dbg_settings_i[DBG_SETS_SSTE];
        unique case(1'b1)
          int_req_int & ctr_decoding_i:
            exc_ctrl_ns = WAIT_CONTROLLER_INT;
          ebrk_insn_i & ctr_decoding_i:
            exc_ctrl_ns = WAIT_CONTROLLER_DBG;
          default:
            if (ext_req_o)
              exc_ctrl_ns = WAIT_CONTROLLER_EXT;
        endcase
      end

      WAIT_CONTROLLER_INT:
      begin
        int_req_o = 1'b1;
        ext_req_o = 1'b0;
        trap_o    = trap_int;
        if (ack_i) begin
          save_cause_o = 1'b1;
          exc_ctrl_ns  = IDLE;
        end
      end

      WAIT_CONTROLLER_EXT:
      begin
        int_req_o = 1'b0;
        ext_req_o = 1'b1;
        trap_o    = trap_int;
        if (ack_i) begin
          save_cause_o = 1'b1;
          exc_ctrl_ns  = IDLE;
        end
      end

      WAIT_CONTROLLER_DBG:
      begin
        exc_ctrl_ns  = IDLE;
        trap_o       = trap_int;
      end

      default:
      begin
        exc_ctrl_ns = IDLE;
      end
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
      exc_ctrl_cs <= IDLE;
    else
      exc_ctrl_cs <= exc_ctrl_ns;
  end


`ifndef SYNTHESIS
  // synopsys translate_off
  // evaluate at falling edge to avoid duplicates during glitches
  always_ff @(negedge clk)
  begin
    if (rst_n && (int_req_o | ext_req_o) && ack_i)
      $display("%t: Entering exception routine.", $time);
  end
  // synopsys translate_on
`endif

endmodule
