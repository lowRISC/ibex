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
// Engineer:       Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Design Name:    Exception Controller                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Exception Controller of the pipelined processor            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import riscv_defines::*;

module riscv_exc_controller
(
  input  logic        clk,
  input  logic        rst_n,

  // handshake signals to controller
  output logic        req_o,
  input  logic        ack_i,

  output logic        trap_o,

  // to IF stage
  output logic  [1:0] pc_mux_o,       // selects target PC for exception
  output logic  [4:0] vec_pc_mux_o,   // selects interrupt handler for vectorized interrupts

  // interrupt lines
  input  logic [31:0] irq_i,          // level-triggered interrupt inputs
  input  logic        irq_enable_i,   // interrupt enable bit from CSR

  // from decoder
  input  logic        ebrk_insn_i,    // ebrk instruction encountered (EBREAK)
  input  logic        illegal_insn_i, // illegal instruction encountered
  input  logic        ecall_insn_i,   // ecall instruction encountered
  input  logic        eret_insn_i,    // eret instruction encountered

  input  logic        lsu_load_err_i,
  input  logic        lsu_store_err_i,

  // to CSR
  output logic [5:0]  cause_o,
  output logic        save_cause_o,

  // from debug unit
  input  logic [DBG_SETS_W-1:0] dbg_settings_i
);


  enum logic [0:0] { IDLE, WAIT_CONTROLLER } exc_ctrl_cs, exc_ctrl_ns;

  logic req_int;
  logic [1:0] pc_mux_int, pc_mux_int_q;
  logic [5:0] cause_int, cause_int_q;

  integer i;


  // a trap towards the debug unit is generated when one of the
  // following conditions are true:
  // - ebreak instruction encountered
  // - single-stepping mode enabled
  // - illegal instruction exception and IIE bit is set
  // - IRQ and INTE bit is set and no exception is currently running
  // - Debuger requests halt
  assign trap_o =       (dbg_settings_i[DBG_SETS_SSTE])
                      | (ecall_insn_i            & dbg_settings_i[DBG_SETS_ECALL])
                      | (lsu_load_err_i          & dbg_settings_i[DBG_SETS_ELSU])
                      | (lsu_store_err_i         & dbg_settings_i[DBG_SETS_ELSU])
                      | (ebrk_insn_i             & dbg_settings_i[DBG_SETS_EBRK])
                      | (illegal_insn_i          & dbg_settings_i[DBG_SETS_EILL])
                      | (irq_enable_i & (|irq_i) & dbg_settings_i[DBG_SETS_IRQ]);

  // request for exception/interrupt
  assign req_int =   ecall_insn_i
                   | lsu_load_err_i
                   | lsu_store_err_i
                   | illegal_insn_i
                   | (irq_enable_i & (|irq_i));


  // Exception cause and ISR address selection
  always_comb
  begin
    cause_int  = 6'b0;
    pc_mux_int = 'x;

    if (irq_enable_i) begin
      // pc_mux_int is a critical signal, so try to get it as soon as possible
      if (|irq_i)
        pc_mux_int = EXC_PC_IRQ;

      for (i = 31; i >= 0; i--)
      begin
        if (irq_i[i]) begin
          cause_int[5]   = 1'b1;
          cause_int[4:0] = $unsigned(i);
        end
      end
    end

    if (ebrk_insn_i) begin
      cause_int  = 6'b0_00011;
    end

    if (ecall_insn_i) begin
      cause_int  = 6'b0_01011;
      pc_mux_int = EXC_PC_ECALL;
    end

    if (illegal_insn_i) begin
      cause_int  = 6'b0_00010;
      pc_mux_int = EXC_PC_ILLINSN;
    end

    if (lsu_load_err_i) begin
      cause_int  = 6'b0_00101;
      pc_mux_int = EXC_PC_LOAD;
    end

    if (lsu_store_err_i) begin
      cause_int  = 6'b0_00111;
      pc_mux_int = EXC_PC_STORE;
    end
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      cause_int_q  <= '0;
      pc_mux_int_q <= '0;
    end else if (exc_ctrl_cs == IDLE && req_int) begin
      // save cause and ISR when new irq request is first sent to controller
      cause_int_q  <= cause_int;
      pc_mux_int_q <= pc_mux_int;
    end
  end


  // Exception cause and mux output (with bypass)
  assign cause_o      = ((exc_ctrl_cs == IDLE && req_int) || ebrk_insn_i) ? cause_int  : cause_int_q;
  assign pc_mux_o     = (exc_ctrl_cs == IDLE && req_int) ? pc_mux_int : pc_mux_int_q;

  // for vectorized IRQ PC mux
  assign vec_pc_mux_o = cause_o[4:0];


  // Exception controller FSM
  always_comb
  begin
    exc_ctrl_ns  = exc_ctrl_cs;
    req_o        = 1'b0;
    save_cause_o = 1'b0;

    unique case (exc_ctrl_cs)
      IDLE:
      begin
        req_o = req_int;

        if (req_int) begin
          exc_ctrl_ns = WAIT_CONTROLLER;

          if (ack_i) begin
            save_cause_o = 1'b1;
            exc_ctrl_ns  = IDLE;
          end
        end
      end

      WAIT_CONTROLLER:
      begin
        req_o = 1'b1;

        if (ack_i) begin
          save_cause_o = 1'b1;
          exc_ctrl_ns  = IDLE;
        end
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
    if (rst_n && req_o && ack_i)
      $display("%t: Entering exception routine.", $time);
  end
  // synopsys translate_on
`endif

endmodule
