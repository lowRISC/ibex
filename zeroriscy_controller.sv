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
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Main controller                                            //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Main CPU controller of the processor                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "zeroriscy_config.sv"

import zeroriscy_defines::*;


module zeroriscy_controller
#(
  parameter REG_ADDR_WIDTH      = 5
)
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        fetch_enable_i,             // Start the decoding
  output logic        ctrl_busy_o,                // Core is busy processing instructions
  output logic        is_decoding_o,              // Core is in decoding state

  // decoder related signals
  output logic        deassert_we_o,              // deassert write enable for next instruction
  input  logic        illegal_insn_i,             // decoder encountered an invalid instruction
  input  logic        mret_insn_i,                // decoder encountered an eret instruction
  input  logic        pipe_flush_i,               // decoder wants to do a pipe flush

  // from IF/ID pipeline
  input  logic        instr_valid_i,              // instruction coming from IF/ID pipeline is valid

  // from prefetcher
  output logic        instr_req_o,                // Start fetching instructions

  // to prefetcher
  output logic        pc_set_o,                   // jump to address set by pc_mux
  output logic [2:0]  pc_mux_o,                   // Selector in the Fetch stage to select the rigth PC (normal, jump ...)

  // LSU
  input  logic        data_misaligned_i,

  // jump/branch signals
  input  logic        branch_in_id_i,             // branch in id
  input  logic        branch_taken_ex_i,          // branch taken signal
  input  logic        branch_set_i,               // branch taken set signal
  input  logic        jump_set_i,                 // jump taken set signal
  input  logic        jump_in_id_i,               // jump is being calculated in ALU

  input  logic        instr_multicyle_i,          // multicycle instructions active

  // Exception Controller Signals
  input  logic        int_req_i,
  input  logic        ext_req_i,
  output logic        exc_ack_o,
  output logic        irq_ack_o,
  output logic        exc_save_if_o,
  output logic        exc_save_id_o,
  output logic        exc_restore_id_o,

  // Debug Signals
  input  logic        dbg_req_i,                  // a trap was hit, so we have to flush EX and WB
  output logic        dbg_ack_o,                  // we stopped and give control to debug now

  input  logic        dbg_stall_i,                // Pipeline stall is requested
  input  logic        dbg_jump_req_i,             // Change PC to value from debug unit

  // forwarding signals
  output logic [1:0]  operand_a_fw_mux_sel_o,     // regfile ra data selector form ID stage

  // stall signals
  output logic        halt_if_o,
  output logic        halt_id_o,

  input  logic        jump_stall_i,
  input  logic        load_stall_i,
  input  logic        branch_stall_i,

  input  logic        id_ready_i,                 // ID stage is ready

  // Performance Counters
  output logic        perf_jump_o,                // we are executing a jump instruction   (j, jr, jal, jalr)
  output logic        perf_jr_stall_o,            // stall due to jump instruction
  output logic        perf_br_stall_o,            // stall due to branch instruction
  output logic        perf_ld_stall_o             // stall due to load instruction
);

  // FSM state encoding

  enum  logic [3:0] { RESET, BOOT_SET, SLEEP, FIRST_FETCH,
                      DECODE, FLUSH,
                      DBG_SIGNAL, DBG_SIGNAL_SLEEP, DBG_WAIT, DBG_WAIT_BRANCH, DBG_WAIT_SLEEP } ctrl_fsm_cs, ctrl_fsm_ns;

  logic exc_req;

`ifndef SYNTHESIS
  // synopsys translate_off
  // make sure we are called later so that we do not generate messages for
  // glitches
  always_ff @(negedge clk)
  begin
    // print warning in case of decoding errors
    if (is_decoding_o && illegal_insn_i) begin
      $display("%t: Illegal instruction (core %0d) at PC 0x%h:", $time, zeroriscy_core.core_id_i,
               zeroriscy_id_stage.pc_id_i);
    end
  end
  // synopsys translate_on
`endif


  ////////////////////////////////////////////////////////////////////////////////////////////
  //   ____ ___  ____  _____    ____ ___  _   _ _____ ____   ___  _     _     _____ ____    //
  //  / ___/ _ \|  _ \| ____|  / ___/ _ \| \ | |_   _|  _ \ / _ \| |   | |   | ____|  _ \   //
  // | |  | | | | |_) |  _|   | |  | | | |  \| | | | | |_) | | | | |   | |   |  _| | |_) |  //
  // | |__| |_| |  _ <| |___  | |__| |_| | |\  | | | |  _ <| |_| | |___| |___| |___|  _ <   //
  //  \____\___/|_| \_\_____|  \____\___/|_| \_| |_| |_| \_\\___/|_____|_____|_____|_| \_\  //
  //                                                                                        //
  ////////////////////////////////////////////////////////////////////////////////////////////

  assign exc_req = int_req_i | ext_req_i;
  always_comb
  begin
    // Default values
    instr_req_o      = 1'b1;

    exc_ack_o        = 1'b0;
    exc_save_if_o    = 1'b0;
    exc_save_id_o    = 1'b0;
    exc_restore_id_o = 1'b0;

    pc_mux_o         = PC_BOOT;
    pc_set_o         = 1'b0;

    ctrl_fsm_ns      = ctrl_fsm_cs;

    ctrl_busy_o      = 1'b1;
    is_decoding_o    = 1'b0;

    halt_if_o        = 1'b0;
    halt_id_o        = 1'b0;
    dbg_ack_o        = 1'b0;

    irq_ack_o        = 1'b0;

    unique case (ctrl_fsm_cs)
      // We were just reset, wait for fetch_enable
      RESET:
      begin
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;

        if (fetch_enable_i == 1'b1)
          ctrl_fsm_ns = BOOT_SET;
        else if (dbg_req_i) begin
          // just go to debug even when we did not yet get a fetch enable
          // this means that the NPC will not be set yet
          ctrl_fsm_ns = DBG_SIGNAL;
        end
      end

      // copy boot address to instr fetch address
      BOOT_SET:
      begin
        instr_req_o   = 1'b1;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;

        ctrl_fsm_ns = FIRST_FETCH;
      end

      // instruction in if_stage is already valid
      SLEEP:
      begin
        // we begin execution when either fetch_enable is high or an
        // interrupt has arrived
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;
        halt_if_o = 1'b1;
        halt_id_o = 1'b1;

        if (dbg_req_i) begin
          // debug request, now we need to check if we should stay sleeping or
          // go to normal processing later
          if (fetch_enable_i || exc_req)
            ctrl_fsm_ns = DBG_SIGNAL;
          else
            ctrl_fsm_ns = DBG_SIGNAL_SLEEP;

        end else begin
          // no debug request incoming, normal execution flow
          if (fetch_enable_i || ext_req_i)
          begin
            ctrl_fsm_ns  = FIRST_FETCH;
          end
        end
      end

      FIRST_FETCH:
      begin
        // Stall because of IF miss
        if ((id_ready_i == 1'b1) && (dbg_stall_i == 1'b0))
        begin
          ctrl_fsm_ns = DECODE;
        end

        // handle exceptions
        if (ext_req_i) begin
          pc_mux_o     = PC_EXCEPTION;
          pc_set_o     = 1'b1;
          exc_ack_o    = 1'b1;
          irq_ack_o    = ext_req_i;
          // TODO: This assumes that the pipeline is always flushed before
          //       going to sleep.
          exc_save_if_o = 1'b1;
        end
      end

      DECODE:
      begin
        is_decoding_o = 1'b0;

          // decode and execute instructions only if the current conditional
          // branch in the EX stage is either not taken, or there is no
          // conditional branch in the EX stage
          if (instr_valid_i)
          begin // now analyze the current instruction in the ID stage
            is_decoding_o = 1'b1;

            unique case (1'b1)

              branch_set_i: begin
                pc_mux_o          = PC_JUMP;
                pc_set_o          = 1'b1;
                if (dbg_req_i)
                  ctrl_fsm_ns = DBG_SIGNAL;
              end
              jump_set_i: begin
                pc_mux_o          = PC_JUMP;
                pc_set_o          = 1'b1;
                if (dbg_req_i)
                  ctrl_fsm_ns = DBG_SIGNAL;
              end
              int_req_i: begin
                ctrl_fsm_ns = FLUSH;
                halt_if_o = 1'b1;
                halt_id_o = 1'b1;
              end
              mret_insn_i: begin
                ctrl_fsm_ns = FLUSH;
                halt_if_o = 1'b1;
                halt_id_o = 1'b1;
              end
              default: begin

                if (ext_req_i & ~instr_multicyle_i & ~branch_in_id_i) begin
                    ctrl_fsm_ns = FLUSH;
                    halt_if_o = 1'b1;
                    halt_id_o = 1'b1;
                end
                // handle WFI instruction, flush pipeline and (potentially) go to
                // sleep TODO: put it in unique case
                else if (pipe_flush_i) begin
                  halt_if_o = 1'b1;
                  halt_id_o = 1'b1;
                  ctrl_fsm_ns = FLUSH;
                end
                else if (dbg_req_i & ~branch_taken_ex_i)
                begin
                  halt_if_o = 1'b1;
                  if (id_ready_i) begin
                    ctrl_fsm_ns = DBG_SIGNAL;
                  end
                end
              end
            endcase
          end

          else if (~instr_valid_i)
          begin
              if (ext_req_i) begin
                pc_mux_o      = PC_EXCEPTION;
                pc_set_o      = 1'b1;
                exc_ack_o     = 1'b1;
                exc_save_if_o = 1'b1;
                irq_ack_o     = 1'b1;
                // we don't have to change our current state here as the prefetch
                // buffer is automatically invalidated, thus the next instruction
                // that is served to the ID stage is the one of the jump to the
                // exception handler
              end
          end
      end

      // now we can signal to the debugger that our pipeline is empty and it
      // can examine our current state
      DBG_SIGNAL:
      begin
        dbg_ack_o  = 1'b1;
        halt_if_o  = 1'b1;

        ctrl_fsm_ns = DBG_WAIT;
      end

      DBG_SIGNAL_SLEEP:
      begin
        dbg_ack_o  = 1'b1;
        halt_if_o  = 1'b1;

        ctrl_fsm_ns = DBG_WAIT_SLEEP;
      end

      // The Debugger is active in this state
      // we wait until it is done and go back to SLEEP
      DBG_WAIT_SLEEP:
      begin
        halt_if_o = 1'b1;

        if (dbg_jump_req_i) begin
          pc_mux_o     = PC_DBG_NPC;
          pc_set_o     = 1'b1;
          ctrl_fsm_ns  = DBG_WAIT;
        end

        if (dbg_stall_i == 1'b0) begin
          ctrl_fsm_ns = SLEEP;
        end
      end

      // The Debugger is active in this state
      // we wait until it is done and go back to DECODE
      DBG_WAIT:
      begin
        halt_if_o = 1'b1;

        if (dbg_jump_req_i) begin
          pc_mux_o     = PC_DBG_NPC;
          pc_set_o     = 1'b1;
          ctrl_fsm_ns  = DBG_WAIT;
        end

        if (dbg_stall_i == 1'b0) begin
          ctrl_fsm_ns = DECODE;
        end
      end


      // flush the pipeline, insert NOP
      FLUSH:
      begin
        halt_if_o = 1'b1;
        halt_id_o = 1'b1;

        if(fetch_enable_i) begin
          if (dbg_req_i) begin
            ctrl_fsm_ns = DBG_SIGNAL;
            if(int_req_i) begin
              //exceptions
              pc_mux_o      = PC_EXCEPTION;
              pc_set_o      = 1'b1;
              exc_ack_o     = 1'b1;
              exc_save_id_o = 1'b1;
            end
          end else begin
            ctrl_fsm_ns = DECODE;
            unique case (1'b1)
              int_req_i: begin
                pc_mux_o          = PC_EXCEPTION;
                pc_set_o          = 1'b1;
                exc_ack_o         = 1'b1;
                exc_save_id_o     = 1'b1;
              end
              mret_insn_i: begin
                pc_mux_o         = PC_ERET;
                pc_set_o         = 1'b1;
                exc_restore_id_o = 1'b1;
              end
              ext_req_i: begin
                pc_mux_o          = PC_EXCEPTION;
                pc_set_o          = 1'b1;
                exc_ack_o         = 1'b1;
                //the instruction in id has been already executed
                exc_save_if_o     = 1'b1;
                irq_ack_o     = 1'b1;
              end
              default: begin
                halt_if_o   = 1'b0;
              end
            endcase
          end
        end else begin //~fetch_enable_i
          //mRET goes back to sleep
          if(mret_insn_i) begin
            //in order to restore the xPIE in xIE
            exc_restore_id_o = 1'b1;
            pc_mux_o         = PC_ERET;
            pc_set_o         = 1'b1;
          end
          if (dbg_req_i) begin
            ctrl_fsm_ns = DBG_SIGNAL_SLEEP;
          end else begin
            ctrl_fsm_ns = SLEEP;
          end
        end
      end

      default: begin
        instr_req_o = 1'b0;
        ctrl_fsm_ns = RESET;
      end
    endcase
  end

  /////////////////////////////////////////////////////////////
  //  ____  _        _ _    ____            _             _  //
  // / ___|| |_ __ _| | |  / ___|___  _ __ | |_ _ __ ___ | | //
  // \___ \| __/ _` | | | | |   / _ \| '_ \| __| '__/ _ \| | //
  //  ___) | || (_| | | | | |__| (_) | | | | |_| | | (_) | | //
  // |____/ \__\__,_|_|_|  \____\___/|_| |_|\__|_|  \___/|_| //
  //                                                         //
  /////////////////////////////////////////////////////////////
  always_comb
  begin

    deassert_we_o  = 1'b0;

    // deassert WE when the core is not decoding instructions
    if (~is_decoding_o)
      deassert_we_o = 1'b1;

    // deassert WE in case of illegal instruction
    if (illegal_insn_i)
      deassert_we_o = 1'b1;
  end

  // Forwarding control unit
  assign operand_a_fw_mux_sel_o = data_misaligned_i ? SEL_MISALIGNED : SEL_REGFILE;

  // update registers
  always_ff @(posedge clk , negedge rst_n)
  begin : UPDATE_REGS
    if ( rst_n == 1'b0 )
    begin
      ctrl_fsm_cs <= RESET;
      //jump_done_q <= 1'b0;
    end
    else
    begin
      ctrl_fsm_cs <= ctrl_fsm_ns;
      // clear when id is valid (no instruction incoming)
      //jump_done_q <= jump_done & (~id_ready_i);
    end
  end

  // Performance Counters
  assign perf_jump_o      = jump_in_id_i;
  assign perf_jr_stall_o  = jump_stall_i;
  assign perf_br_stall_o  = branch_stall_i;
  assign perf_ld_stall_o  = load_stall_i;


  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
`ifndef VERILATOR
  assert property (
    @(posedge clk) (~(dbg_req_i & ext_req_i)) ) else $warning("Both dbg_req_i and ext_req_i are active");
`endif
endmodule // controller
