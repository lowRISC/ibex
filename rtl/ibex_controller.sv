// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Main controller                                            //
// Project Name:   ibex                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Main CPU controller of the processor                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

/**
 * Main CPU controller of the processor
 */
module ibex_controller (
    input  logic                      clk_i,
    input  logic                      rst_ni,

    input  logic                      fetch_enable_i,        // start decoding
    output logic                      ctrl_busy_o,           // core is busy processing instrs
    output logic                      first_fetch_o,         // core is at the FIRST FETCH stage
    output logic                      is_decoding_o,         // core is in decoding state

    // decoder related signals
    output logic                      deassert_we_o,         // deassert write enable for next
                                                             // instr

    input  logic                      illegal_insn_i,        // decoder has an invalid instr
    input  logic                      ecall_insn_i,          // decoder has ECALL instr
    input  logic                      mret_insn_i,           // decoder has MRET instr
    input  logic                      dret_insn_i,           // decoder has DRET instr
    input  logic                      pipe_flush_i,          // decoder wants to do a pipe flush
    input  logic                      ebrk_insn_i,           // decoder has EBREAK instr
    input  logic                      csr_status_i,          // decoder has CSR status instr

    // from IF/ID pipeline
    input  logic                      instr_valid_i,         // instruction coming from IF/ID stage
                                                             // is valid

    // from prefetcher
    output logic                      instr_req_o,           // start fetching instructions

    // to prefetcher
    output logic                      pc_set_o,              // jump to address set by pc_mux
    output ibex_defines::pc_sel_e     pc_mux_o,              // IF stage fetch address selector
                                                             // (boot, normal, exception...)
    output ibex_defines::exc_pc_sel_e exc_pc_mux_o,          // IF stage selector for exception PC

    // LSU
    input  logic                      data_misaligned_i,
    input  logic                      load_err_i,
    input  logic                      store_err_i,

    // jump/branch signals
    input  logic                      branch_in_id_i,        // branch in id
    input  logic                      branch_set_i,          // branch taken set signal
    input  logic                      jump_set_i,            // jump taken set signal

    input  logic                      instr_multicyle_i,     // multicycle instructions active

    // External Interrupt Req Signals, used to wake up from wfi even if the interrupt is not taken
    input  logic                      irq_i,
    // Interrupt Controller Signals
    input  logic                      irq_req_ctrl_i,
    input  logic [4:0]                irq_id_ctrl_i,
    input  logic                      m_IE_i,                // interrupt enable bit from CSR
                                                             // (M mode)

    output logic                      irq_ack_o,
    output logic [4:0]                irq_id_o,

    output ibex_defines::exc_cause_e  exc_cause_o,
    output logic                      exc_ack_o,
    output logic                      exc_kill_o,

    // Debug Signal
    input  logic                      debug_req_i,
    output ibex_defines::dbg_cause_e  debug_cause_o,
    output logic                      debug_csr_save_o,
    input  logic                      debug_single_step_i,
    input  logic                      debug_ebreakm_i,

    output logic                      csr_save_if_o,
    output logic                      csr_save_id_o,
    output ibex_defines::exc_cause_e  csr_cause_o,
    output logic                      csr_restore_mret_id_o,
    output logic                      csr_restore_dret_id_o,
    output logic                      csr_save_cause_o,

    // forwarding signals
    output ibex_defines::op_fw_sel_e  operand_a_fw_mux_sel_o, // regfile ra selector for ID stage

    // stall signals
    output logic                      halt_if_o,
    output logic                      halt_id_o,

    input  logic                      id_ready_i,             // ID stage is ready

    // Performance Counters
    output logic                      perf_jump_o,            // we are executing a jump
                                                              // instruction (j, jr, jal, jalr)
    output logic                      perf_tbranch_o          // we are executing a taken branch
                                                              // instruction
);
  import ibex_defines::*;

  // FSM state encoding
  typedef enum logic [3:0] {
    RESET, BOOT_SET, WAIT_SLEEP, SLEEP, FIRST_FETCH, DECODE, FLUSH,
    IRQ_TAKEN, DBG_TAKEN_IF, DBG_TAKEN_ID
  } ctrl_fsm_e;

  ctrl_fsm_e ctrl_fsm_cs, ctrl_fsm_ns;

  logic irq_enable_int;

  logic debug_mode_q, debug_mode_n;
  logic load_err_q, load_err_n;
  logic store_err_q, store_err_n;

`ifndef SYNTHESIS
  // synopsys translate_off
  // make sure we are called later so that we do not generate messages for
  // glitches
  always_ff @(negedge clk_i) begin
    // print warning in case of decoding errors
    if (is_decoding_o && illegal_insn_i) begin
      $display("%t: Illegal instruction (core %0d) at PC 0x%h: 0x%h", $time, ibex_core.core_id_i,
               ibex_id_stage.pc_id_i, ibex_id_stage.instr_rdata_i);
    end
  end
  // synopsys translate_on
`endif


  /////////////////////
  // Core controller //
  /////////////////////

  always_comb begin
    // Default values
    instr_req_o            = 1'b1;

    exc_ack_o              = 1'b0;
    exc_kill_o             = 1'b0;

    csr_save_if_o          = 1'b0;
    csr_save_id_o          = 1'b0;
    csr_restore_mret_id_o  = 1'b0;

    csr_restore_dret_id_o  = 1'b0;

    csr_save_cause_o       = 1'b0;

    exc_cause_o            = EXC_CAUSE_INSN_ADDR_MISA; // = 6'h00
    exc_pc_mux_o           = EXC_PC_IRQ;

    csr_cause_o            = EXC_CAUSE_INSN_ADDR_MISA; // = 6'h00

    pc_mux_o               = PC_BOOT;
    pc_set_o               = 1'b0;

    ctrl_fsm_ns            = ctrl_fsm_cs;

    ctrl_busy_o            = 1'b1;
    is_decoding_o          = 1'b0;
    first_fetch_o          = 1'b0;

    halt_if_o              = 1'b0;
    halt_id_o              = 1'b0;
    irq_ack_o              = 1'b0;
    irq_id_o               = irq_id_ctrl_i;
    irq_enable_int         = m_IE_i;

    debug_csr_save_o       = 1'b0;
    debug_cause_o          = DBG_CAUSE_EBREAK;
    debug_mode_n           = debug_mode_q;

    load_err_n             = 1'b0;
    store_err_n            = 1'b0;

    perf_tbranch_o         = 1'b0;
    perf_jump_o            = 1'b0;

    unique case (ctrl_fsm_cs)
      // We were just reset, wait for fetch_enable
      RESET: begin
        instr_req_o   = 1'b0;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;
        if (fetch_enable_i) begin
          ctrl_fsm_ns = BOOT_SET;
        end
      end

      // copy boot address to instr fetch address
      BOOT_SET: begin
        instr_req_o   = 1'b1;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;

        ctrl_fsm_ns = FIRST_FETCH;
      end

      WAIT_SLEEP: begin
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;
        halt_if_o     = 1'b1;
        halt_id_o     = 1'b1;
        ctrl_fsm_ns   = SLEEP;
      end

      // instruction in if_stage is already valid
      SLEEP: begin
        // we begin execution when an
        // interrupt has arrived
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;
        halt_if_o     = 1'b1;
        halt_id_o     = 1'b1;

        // normal execution flow
        // in debug mode or single step mode we leave immediately (wfi=nop)
        if (irq_i || debug_req_i || debug_mode_q || debug_single_step_i) begin
          ctrl_fsm_ns  = FIRST_FETCH;
        end
      end

      FIRST_FETCH: begin
        first_fetch_o = 1'b1;
        // Stall because of IF miss
        if (id_ready_i) begin
          ctrl_fsm_ns = DECODE;
        end

        // handle interrupts
        if (irq_req_ctrl_i && irq_enable_int) begin
          // This assumes that the pipeline is always flushed before
          // going to sleep.
          ctrl_fsm_ns = IRQ_TAKEN;
          halt_if_o   = 1'b1;
          halt_id_o   = 1'b1;
        end

        // enter debug mode
        if (debug_req_i && !debug_mode_q) begin
          ctrl_fsm_ns  = DBG_TAKEN_IF;
          halt_if_o    = 1'b1;
          halt_id_o    = 1'b1;
        end
      end

      DECODE: begin
        is_decoding_o = 1'b0;

        /*
         * TODO: What should happen on
         * instr_valid_i && (instr_multicyle_i || branch_in_id_i)?
         * Let the instruction finish executing before serving debug or
         * interrupt requests?
         */

        unique case (1'b1)
          debug_req_i && !debug_mode_q: begin
            // Enter debug mode from external request
            ctrl_fsm_ns   = DBG_TAKEN_ID;
            halt_if_o     = 1'b1;
            halt_id_o     = 1'b1;
          end

          irq_req_ctrl_i && irq_enable_int && !debug_req_i && !debug_mode_q: begin
            // Serve an interrupt (not in debug mode)
            ctrl_fsm_ns = IRQ_TAKEN;
            halt_if_o   = 1'b1;
            halt_id_o   = 1'b1;
          end

          default: begin
            exc_kill_o    = irq_req_ctrl_i & ~instr_multicyle_i & ~branch_in_id_i;

            if (instr_valid_i) begin
              // analyze the current instruction in the ID stage
              is_decoding_o = 1'b1;

              if (branch_set_i || jump_set_i) begin
                pc_mux_o       = PC_JUMP;
                pc_set_o       = 1'b1;

                perf_tbranch_o = branch_set_i;
                perf_jump_o    = jump_set_i;
              end else if (mret_insn_i || dret_insn_i || ecall_insn_i || pipe_flush_i ||
                           ebrk_insn_i || illegal_insn_i || csr_status_i ||
                           store_err_i || load_err_i) begin
                ctrl_fsm_ns = FLUSH;
                halt_if_o   = 1'b1;
                halt_id_o   = 1'b1;
                load_err_n  = load_err_i;
                store_err_n = store_err_i;
              end
            end
          end
        endcase

        // Single stepping
        // prevent any more instructions from executing
        if (debug_single_step_i && !debug_mode_q) begin
          halt_if_o = 1'b1;
          ctrl_fsm_ns = DBG_TAKEN_IF;
        end
      end

      IRQ_TAKEN: begin
        pc_mux_o          = PC_EXCEPTION;
        pc_set_o          = 1'b1;

        exc_pc_mux_o      = EXC_PC_IRQ;
        exc_cause_o       = exc_cause_e'({1'b0, irq_id_ctrl_i});

        csr_save_cause_o  = 1'b1;
        csr_cause_o       = exc_cause_e'({1'b1, irq_id_ctrl_i});

        csr_save_if_o     = 1'b1;

        irq_ack_o         = 1'b1;
        exc_ack_o         = 1'b1;

        ctrl_fsm_ns       = DECODE;
      end

      // Enter debug mode and save PC in IF to DPC
      DBG_TAKEN_IF:
      begin
        // Jump to debug exception handler in debug memory
        pc_mux_o          = PC_EXCEPTION;
        pc_set_o          = 1'b1;
        exc_pc_mux_o      = EXC_PC_DBD;

        csr_save_if_o   = 1'b1;
        debug_csr_save_o  = 1'b1;

        csr_save_cause_o  = 1'b1;
        if (debug_single_step_i) begin
          debug_cause_o = DBG_CAUSE_STEP;
        end else if (debug_req_i) begin
          debug_cause_o = DBG_CAUSE_HALTREQ;
        end else if (ebrk_insn_i) begin
          debug_cause_o = DBG_CAUSE_EBREAK;
        end

        // We've entered debug mode
        debug_mode_n    = 1'b1;

        ctrl_fsm_ns     = DECODE;
      end

      // We enter this state when we encounter
      // 1. ebreak during debug mode
      // 2. ebreak with forced entry into debug mode (ebreakm or ebreaku set).
      // 3. halt request during decode
      // Regular ebreak's go through FLUSH_EX and FLUSH_WB.
      // For 1. we don't update dcsr and dpc while for 2. and 3. we do
      // (debug-spec p.39). Critically dpc is set to the address of ebreak and
      // not to the next instruction's (which is why we save the pc in id).
      DBG_TAKEN_ID: begin
        // Jump to debug exception handler in debug memory
        pc_mux_o          = PC_EXCEPTION;
        pc_set_o          = 1'b1;
        exc_pc_mux_o      = EXC_PC_DBD;

        // Update DCSR and DPC
        if ((ebrk_insn_i && debug_ebreakm_i && !debug_mode_q) || // ebreak with forced entry
            (debug_req_i && !debug_mode_q)) begin // halt request

          // DPC (set to the address of the ebreak, i.e. set to PC in ID stage)
          csr_save_cause_o = 1'b1;
          csr_save_id_o    = 1'b1;

          // DCSR
          debug_csr_save_o = 1'b1;
          if (debug_req_i) begin
            debug_cause_o = DBG_CAUSE_HALTREQ;
          end else if (ebrk_insn_i) begin
            debug_cause_o = DBG_CAUSE_EBREAK;
          end
        end

        // We've entered debug mode
        debug_mode_n = 1'b1;

        ctrl_fsm_ns  = DECODE;
      end

      // flush the pipeline, insert NOP
      FLUSH: begin

        halt_if_o = 1'b1;
        halt_id_o = 1'b1;

        if (!pipe_flush_i) begin
          ctrl_fsm_ns = DECODE;
        end else begin
          ctrl_fsm_ns = WAIT_SLEEP;
        end

        unique case(1'b1)
          ecall_insn_i: begin
            //ecall
            pc_mux_o              = PC_EXCEPTION;
            pc_set_o              = 1'b1;
            csr_save_id_o         = 1'b1;
            csr_save_cause_o      = 1'b1;
            exc_pc_mux_o          = EXC_PC_ECALL;
            exc_cause_o           = EXC_CAUSE_ECALL_MMODE;
            csr_cause_o           = EXC_CAUSE_ECALL_MMODE;
          end
          illegal_insn_i: begin
            //exceptions
            pc_mux_o              = PC_EXCEPTION;
            pc_set_o              = 1'b1;
            csr_save_id_o         = 1'b1;
            csr_save_cause_o      = 1'b1;
            if (debug_mode_q) begin
              exc_pc_mux_o          = EXC_PC_DBGEXC;
            end else begin
              exc_pc_mux_o          = EXC_PC_ILLINSN;
            end
            exc_cause_o           = EXC_CAUSE_ILLEGAL_INSN;
            csr_cause_o           = EXC_CAUSE_ILLEGAL_INSN;
          end
          mret_insn_i: begin
            //mret
            pc_mux_o              = PC_ERET;
            pc_set_o              = 1'b1;
            csr_restore_mret_id_o = 1'b1;
          end
          dret_insn_i: begin
            //dret
            pc_mux_o              = PC_DRET;
            pc_set_o              = 1'b1;
            debug_mode_n          = 1'b0;
            csr_restore_dret_id_o = 1'b1;
          end
          ebrk_insn_i: begin
            //ebreak
            if (debug_mode_q) begin
              /*
               * ebreak in debug mode re-enters debug mode
               *
               * "The only exception is ebreak. When that is executed in Debug
               * Mode, it halts the hart again but without updating dpc or
               * dcsr." [RISC-V Debug Specification v0.13.1, p. 41]
               */
              ctrl_fsm_ns = DBG_TAKEN_ID;
            end else if (debug_ebreakm_i) begin
              /*
               * dcsr.ebreakm == 1:
               * "ebreak instructions in M-mode enter Debug Mode."
               * (Debug Spec, p. 44)
               */
              ctrl_fsm_ns = DBG_TAKEN_ID;
            end else begin
              /*
               * "The EBREAK instruction is used by debuggers to cause control
               * to be transferred back to a debugging environment. It
               * generates a breakpoint exception and performs no other
               * operation. [...] ECALL and EBREAK cause the receiving
               * privilege mode’s epc register to be set to the address of the
               * ECALL or EBREAK instruction itself, not the address of the
               * following instruction." (Privileged Spec, p. 40)
               */
              pc_mux_o              = PC_EXCEPTION;
              pc_set_o              = 1'b1;
              csr_save_id_o         = 1'b1;
              csr_save_cause_o      = 1'b1;
              exc_pc_mux_o          = EXC_PC_BREAKPOINT;
              exc_cause_o           = EXC_CAUSE_BREAKPOINT;
              csr_cause_o           = EXC_CAUSE_BREAKPOINT;
            end
          end
          load_err_q: begin
            pc_mux_o         = PC_EXCEPTION;
            pc_set_o         = 1'b1;
            csr_save_id_o    = 1'b1;
            csr_save_cause_o = 1'b1;
            exc_pc_mux_o     = EXC_PC_LOAD;
            exc_cause_o      = EXC_CAUSE_LOAD_ACCESS_FAULT;
            csr_cause_o      = EXC_CAUSE_LOAD_ACCESS_FAULT;
          end
          store_err_q: begin
            pc_mux_o         = PC_EXCEPTION;
            pc_set_o         = 1'b1;
            csr_save_id_o    = 1'b1;
            csr_save_cause_o = 1'b1;
            exc_pc_mux_o     = EXC_PC_STORE;
            exc_cause_o      = EXC_CAUSE_STORE_ACCESS_FAULT;
            csr_cause_o      = EXC_CAUSE_STORE_ACCESS_FAULT;
          end

          default:;
        endcase
      end

      default: begin
        instr_req_o = 1'b0;
        ctrl_fsm_ns = ctrl_fsm_e'(1'bX);
      end
    endcase
  end

  ///////////////////
  // Stall control //
  ///////////////////

  // deassert WE when the core is not decoding instructions
  // or in case of illegal instruction
  assign deassert_we_o = ~is_decoding_o | illegal_insn_i;

  // Forwarding control unit
  assign operand_a_fw_mux_sel_o = data_misaligned_i ? SEL_MISALIGNED : SEL_REGFILE;

  // update registers
  always_ff @(posedge clk_i or negedge rst_ni) begin : update_regs
    if (!rst_ni) begin
      ctrl_fsm_cs  <= RESET;
      debug_mode_q <= 1'b0;
      load_err_q   <= 1'b0;
      store_err_q  <= 1'b0;
    end else begin
      ctrl_fsm_cs  <= ctrl_fsm_ns;
      debug_mode_q <= debug_mode_n;
      load_err_q   <= load_err_n;
      store_err_q  <= store_err_n;
    end
  end

endmodule // controller
