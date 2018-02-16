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
  output logic        first_fetch_o,              // Core is at the FIRST FETCH stage
  output logic        is_decoding_o,              // Core is in decoding state

  // decoder related signals
  output logic        deassert_we_o,              // deassert write enable for next instruction

  input  logic        illegal_insn_i,             // decoder encountered an invalid instruction
  input  logic        ecall_insn_i,               // ecall encountered an mret instruction
  input  logic        mret_insn_i,                // decoder encountered an mret instruction
  input  logic        pipe_flush_i,               // decoder wants to do a pipe flush
  input  logic        ebrk_insn_i,                // decoder encountered an ebreak instruction
  input  logic        csr_status_i,              // decoder encountered an csr status instruction

  // from IF/ID pipeline
  input  logic        instr_valid_i,              // instruction coming from IF/ID pipeline is valid

  // from prefetcher
  output logic        instr_req_o,                // Start fetching instructions

  // to prefetcher
  output logic        pc_set_o,                   // jump to address set by pc_mux
  output logic [2:0]  pc_mux_o,                   // Selector in the Fetch stage to select the rigth PC (normal, jump ...)
  output logic [1:0]  exc_pc_mux_o,               // Selects target PC for exception

  // LSU
  input  logic        data_misaligned_i,

  // jump/branch signals
  input  logic        branch_in_id_i,             // branch in id
  input  logic        branch_taken_ex_i,          // branch taken signal
  input  logic        branch_set_i,               // branch taken set signal
  input  logic        jump_set_i,                 // jump taken set signal

  input  logic        instr_multicyle_i,          // multicycle instructions active

  // External Interrupt Req Signals, used to wake up from wfi even if the interrupt is not taken
  input  logic        irq_i,
  // Interrupt Controller Signals
  input  logic        irq_req_ctrl_i,
  input  logic [4:0]  irq_id_ctrl_i,
  input  logic        m_IE_i,                     // interrupt enable bit from CSR (M mode)

  output logic        irq_ack_o,
  output logic [4:0]  irq_id_o,

  output logic [5:0]  exc_cause_o,
  output logic        exc_ack_o,
  output logic        exc_kill_o,

  output logic        csr_save_if_o,
  output logic        csr_save_id_o,
  output logic [5:0]  csr_cause_o,
  output logic        csr_restore_mret_id_o,
  output logic        csr_save_cause_o,

  // Debug Signals
  input  logic        dbg_req_i,                  // a trap was hit, so we have to flush EX and WB
  output logic        dbg_ack_o,                  // we stopped and give control to debug now

  input  logic        dbg_stall_i,                // Pipeline stall is requested
  input  logic        dbg_jump_req_i,             // Change PC to value from debug unit

  input  logic [DBG_SETS_W-1:0] dbg_settings_i,
  output logic        dbg_trap_o,

  // forwarding signals
  output logic [1:0]  operand_a_fw_mux_sel_o,     // regfile ra data selector form ID stage

  // stall signals
  output logic        halt_if_o,
  output logic        halt_id_o,

  input  logic        id_ready_i,                 // ID stage is ready

  // Performance Counters
  output logic        perf_jump_o,                // we are executing a jump instruction   (j, jr, jal, jalr)
  output logic        perf_tbranch_o             // we are executing a taken branch instruction
);

  // FSM state encoding
  enum  logic [3:0] { RESET, BOOT_SET, WAIT_SLEEP, SLEEP, FIRST_FETCH,
                      DECODE, FLUSH, IRQ_TAKEN,
                      DBG_SIGNAL, DBG_SIGNAL_SLEEP, DBG_WAIT, DBG_WAIT_BRANCH } ctrl_fsm_cs, ctrl_fsm_ns;

  logic irq_enable_int;

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


  always_comb
  begin
    // Default values
    instr_req_o            = 1'b1;

    exc_ack_o              = 1'b0;
    exc_kill_o             = 1'b0;

    csr_save_if_o          = 1'b0;
    csr_save_id_o          = 1'b0;
    csr_restore_mret_id_o  = 1'b0;
    csr_save_cause_o       = 1'b0;

    exc_cause_o            = '0;
    exc_pc_mux_o           = EXC_PC_IRQ;

    csr_cause_o            = '0;

    pc_mux_o               = PC_BOOT;
    pc_set_o               = 1'b0;

    ctrl_fsm_ns            = ctrl_fsm_cs;

    ctrl_busy_o            = 1'b1;
    is_decoding_o          = 1'b0;
    first_fetch_o          = 1'b0;

    halt_if_o              = 1'b0;
    halt_id_o              = 1'b0;
    dbg_ack_o              = 1'b0;
    irq_ack_o              = 1'b0;
    irq_id_o               = irq_id_ctrl_i;
    irq_enable_int         = m_IE_i;

    // a trap towards the debug unit is generated when one of the
    // following conditions are true:
    // - ebreak instruction encountered
    // - single-stepping mode enabled
    // - illegal instruction exception and IIE bit is set
    // - IRQ and INTE bit is set and no exception is currently running
    // - Debuger requests halt
    dbg_trap_o             = 1'b0;

    perf_tbranch_o         = 1'b0;
    perf_jump_o            = 1'b0;

    unique case (ctrl_fsm_cs)
      // We were just reset, wait for fetch_enable
      RESET:
      begin
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

      WAIT_SLEEP:
      begin
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;
        halt_if_o     = 1'b1;
        halt_id_o     = 1'b1;
        ctrl_fsm_ns   = SLEEP;
      end

      // instruction in if_stage is already valid
      SLEEP:
      begin
        // we begin execution when an
        // interrupt has arrived
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;
        halt_if_o     = 1'b1;
        halt_id_o     = 1'b1;
        dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];

        if (dbg_req_i) begin
          // debug request, now we need to check if we should stay sleeping or
          // go to normal processing later
            ctrl_fsm_ns = DBG_SIGNAL_SLEEP;

        end else begin
          // no debug request incoming, normal execution flow
          // here transparent interrupts are checked to wake up from wfi
          if (irq_i)
          begin
            ctrl_fsm_ns  = FIRST_FETCH;
          end
        end
      end

      FIRST_FETCH:
      begin
        first_fetch_o = 1'b1;
        // Stall because of IF miss
        if ((id_ready_i == 1'b1) && (dbg_stall_i == 1'b0))
        begin
          ctrl_fsm_ns = DECODE;
        end

        if (irq_req_ctrl_i & irq_enable_int) begin
          // This assumes that the pipeline is always flushed before
          // going to sleep.
          ctrl_fsm_ns = IRQ_TAKEN;
          halt_if_o   = 1'b1;
          halt_id_o   = 1'b1;
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

              if (branch_set_i & ~jump_set_i & ~(mret_insn_i | ecall_insn_i | pipe_flush_i | ebrk_insn_i | illegal_insn_i | csr_status_i))
              begin
                pc_mux_o          = PC_JUMP;
                pc_set_o          = 1'b1;
                perf_tbranch_o    = 1'b1;
                dbg_trap_o        = dbg_settings_i[DBG_SETS_SSTE];
                if (dbg_req_i)
                  ctrl_fsm_ns = DBG_SIGNAL;
              end
              else if (~branch_set_i & jump_set_i & ~(mret_insn_i | ecall_insn_i | pipe_flush_i | ebrk_insn_i | illegal_insn_i | csr_status_i))
              begin
                pc_mux_o          = PC_JUMP;
                pc_set_o          = 1'b1;
                perf_jump_o       = 1'b1;
                dbg_trap_o        = dbg_settings_i[DBG_SETS_SSTE];
              end
              else if (~branch_set_i & ~jump_set_i & (mret_insn_i | ecall_insn_i | pipe_flush_i | ebrk_insn_i | illegal_insn_i | csr_status_i))
              begin
                ctrl_fsm_ns = FLUSH;
                halt_if_o   = 1'b1;
                halt_id_o   = 1'b1;
              end
              else
              begin
                dbg_trap_o = dbg_settings_i[DBG_SETS_SSTE];

                if ((irq_req_ctrl_i & irq_enable_int & ~instr_multicyle_i & ~branch_in_id_i) & ~(dbg_req_i & ~branch_taken_ex_i))
                begin
                    ctrl_fsm_ns = IRQ_TAKEN;
                    halt_if_o   = 1'b1;
                    halt_id_o   = 1'b1;
                end
                else if (~(irq_req_ctrl_i & irq_enable_int & ~instr_multicyle_i & ~branch_in_id_i) & (dbg_req_i & ~branch_taken_ex_i))
                begin
                    halt_if_o = 1'b1;
                    if (id_ready_i) begin
                      ctrl_fsm_ns = DBG_SIGNAL;
                    end
                end
                else
                    exc_kill_o    = irq_req_ctrl_i & ~instr_multicyle_i & ~branch_in_id_i ? 1'b1 : 1'b0;
              end
          end
          else //~instr_valid_i
          begin
              if (irq_req_ctrl_i & irq_enable_int) begin
                ctrl_fsm_ns = IRQ_TAKEN;
                halt_if_o   = 1'b1;
                halt_id_o   = 1'b1;
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

        ctrl_fsm_ns = DBG_WAIT;
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

      IRQ_TAKEN:
      begin
        pc_mux_o          = PC_EXCEPTION;
        pc_set_o          = 1'b1;

        exc_pc_mux_o      = EXC_PC_IRQ;
        exc_cause_o       = {1'b0,irq_id_ctrl_i};

        csr_save_cause_o  = 1'b1;
        csr_cause_o       = {1'b1,irq_id_ctrl_i};

        csr_save_if_o     = 1'b1;

        irq_ack_o         = 1'b1;
        exc_ack_o         = 1'b1;

        ctrl_fsm_ns       = DECODE;
      end

      // flush the pipeline, insert NOP
      FLUSH:
      begin

        halt_if_o = 1'b1;
        halt_id_o = 1'b1;

        ctrl_fsm_ns = dbg_req_i ? DBG_SIGNAL : DECODE;

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
              dbg_trap_o            = dbg_settings_i[DBG_SETS_ECALL] | dbg_settings_i[DBG_SETS_SSTE];
          end
          illegal_insn_i: begin
              //exceptions
              pc_mux_o              = PC_EXCEPTION;
              pc_set_o              = 1'b1;
              csr_save_id_o         = 1'b1;
              csr_save_cause_o      = 1'b1;
              exc_pc_mux_o          = EXC_PC_ILLINSN;
              exc_cause_o           = EXC_CAUSE_ILLEGAL_INSN;
              csr_cause_o           = EXC_CAUSE_ILLEGAL_INSN;
              dbg_trap_o            = dbg_settings_i[DBG_SETS_EILL] | dbg_settings_i[DBG_SETS_SSTE];
          end
          mret_insn_i: begin
              //mret
              pc_mux_o              = PC_ERET;
              pc_set_o              = 1'b1;
              csr_restore_mret_id_o = 1'b1;
              dbg_trap_o            = dbg_settings_i[DBG_SETS_SSTE];
          end
          ebrk_insn_i: begin
              dbg_trap_o    = 1'b1;//dbg_settings_i[DBG_SETS_EBRK] | dbg_settings_i[DBG_SETS_SSTE];;
              exc_cause_o   = EXC_CAUSE_BREAKPOINT;
          end
          csr_status_i: begin
              dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];
          end
          pipe_flush_i: begin
              dbg_trap_o    = dbg_settings_i[DBG_SETS_SSTE];
          end
          default:;
        endcase

        if(~pipe_flush_i) begin
          if(dbg_req_i)
            ctrl_fsm_ns = DBG_SIGNAL;
          else
            ctrl_fsm_ns = DECODE;
        end else begin
          if(dbg_req_i)
            ctrl_fsm_ns = DBG_SIGNAL_SLEEP;
          else
            ctrl_fsm_ns = WAIT_SLEEP;
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


  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
`ifndef VERILATOR
  assert property (
    @(posedge clk) (~(dbg_req_i & irq_req_ctrl_i)) ) else $warning("Both dbg_req_i and irq_req_ctrl_i are active");
`endif
endmodule // controller
