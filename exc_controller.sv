////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    20/01/2015                                                 //
// Design Name:    Pipelined OpenRISC Processor                               //
// Module Name:    exc_controller.sv                                          //
// Project Name:   OR10N                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Exception Controller of the pipelined processor            //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"

module exc_controller
(
   input  logic        clk,
   input  logic        rst_n,

   input  logic        fetch_enable_i,

   // to IF stage
   output logic        exc_pc_sel_o,               // influences next PC, if set exception PC is used
   output logic [1:0]  exc_pc_mux_o,               // Selector in the Fetch stage to select the rigth exception PC
   output logic        force_nop_o,                // Force a Nop (Bubble) in the Fetch stage

   // hwloop signals
   output logic        hwloop_enable_o,             // '1' if pc is valid (interrupt related signal)

   // Interrupt signals
   input  logic        irq_i,                       // level-triggered IR line
   input  logic        irq_nm_i,                    // level-triggered IR line for non-maskable IRQ
   input  logic        irq_enable_i,                // global interrupt enable
   output logic        irq_present_o,               // tells the controller to start fetching instructions if asleep

   // SPR
   output logic        save_pc_if_o,                // saves current_pc_if before entering interrupt routine
   output logic        save_pc_id_o,                // saves current_pc_id before entering interrupt routine
   output logic        save_sr_o,                   // saves status register
   output logic        set_dsx_o,                   // set delay slot flag

   // Controller
   input  logic        core_busy_i,                 // Is the controller currently in the IDLE state?
   input  logic [1:0]  jump_in_id_i,                // jump instruction in ID stage
   input  logic [1:0]  jump_in_ex_i,                // jump instruction in EX stage
   input  logic        stall_id_i,                  // Stall ID stage
   input  logic        illegal_insn_i,              // Illegal instruction encountered in ID stage
   input  logic        trap_insn_i,                 // Trap instruction encountered in ID stage
   input  logic        pipe_flush_i,                // pipe flush requested by controller
   output logic        pc_valid_o,                  // is the PC in the IF stage currently valid?
   input  logic        clear_isr_running_i,         // exit ISR routine

   // Debug Unit Signals
   input  logic        dbg_flush_pipe_i,            // Pipe flush requested
   output logic        pipe_flushed_o,              // Pipe is flushed
   input  logic        dbg_st_en_i,                 // Single-step trace mode enabled
   input  logic [1:0]  dbg_dsr_i,                   // Debug Stop Register
   input  logic        dbg_stall_i,                 // Pipeline stall is requested
   input  logic        dbg_set_npc_i,               // Change PC to value from debug unit
   output logic        dbg_trap_o                   // Software Trap in ID (l.trap)
);

  // Exception unit state encoding
  enum  logic [2:0]  { Idle, SingleStep, NopDelay, NopDelayIR, NopID, NopEX, NopWB}  exc_fsm_cs, exc_fsm_ns;
  enum  logic [2:0]  { ExcNone, ExcST, ExcIR, ExcTrap, ExcFlush, ExcDbgFlush, ExcIllegalInsn } exc_reason_p, exc_reason_n, exc_reason;

  // Registers
  logic       exc_running_p, exc_running_n;

  logic       clear_exc_reason;

  // disable hardware loops when nops are inserted or the controller is not active
  assign hwloop_enable_o = (~force_nop_o) | (~core_busy_i);

  /////////////////////////////////////////////
  //   ____                     _            //
  //  |  _ \  ___  ___ ___   __| | ___ _ __  //
  //  | | | |/ _ \/ __/ _ \ / _` |/ _ \ '__| //
  //  | |_| |  __/ (_| (_) | (_| |  __/ |    //
  //  |____/ \___|\___\___/ \__,_|\___|_|    //
  //                                         //
  /////////////////////////////////////////////

  // a trap towards the debug unit is generated when one of the
  // following conditions are true:
  // - l.trap instruction encountered
  // - single-stepping mode enabled (after one instruction is executed)
  // - illegal instruction exception and IIE bit is set
  // - IRQ and INTE bit is set and no exception is currently running
  assign dbg_trap_o    = trap_insn_i || dbg_st_en_i || (illegal_insn_i & dbg_dsr_i[`DSR_IIE]) || (irq_present_o & dbg_dsr_i[`DSR_INTE] & (~exc_running_p));

  assign irq_present_o = (irq_i || irq_nm_i) & irq_enable_i;

  // Decoder for exc_reason signal
  // this signal tells the exception controller which is the exception
  // with highest priority at the moment
  // The decoder also takes care that no nested exceptions are performed
  always_comb
  begin
    exc_reason = ExcNone;

    if (dbg_st_en_i == 1'b1)
    begin
      // Single-step trace mode
      exc_reason = ExcST;
    end
    else if ((trap_insn_i == 1'b1) || (dbg_flush_pipe_i == 1'b1))
    begin
      // flushing pipeline because of l.trap instruction
      exc_reason = ExcTrap;
    end
    else if (illegal_insn_i == 1'b1)
    begin
      // if the IIE bit in the Debug Stop Register is set, we transfer
      // the control to the debug interface
      // otherwise we jump to the interrupt handler, if we are not
      // already in an interrupt handler
      if (dbg_dsr_i[`DSR_IIE] == 1'b1)
        exc_reason = ExcTrap;
      else if (exc_running_p == 1'b0)
        exc_reason = ExcIllegalInsn;
    end
    else if ((irq_present_o == 1'b1) && (exc_running_p == 1'b0))
    begin
      // an interrupt is present, flush pipeline, execute pending delay slots
      // and then call the interrupt handler
      // or if the INTE bit is set, transfer the control to the debug interface
      if (dbg_dsr_i[`DSR_INTE] == 1'b1)
        exc_reason = ExcTrap;
      else
        exc_reason = ExcIR;
    end
    else if(pipe_flush_i == 1'b1)
    begin
      // flushing pipeline because of l.psync
      exc_reason = ExcFlush;
    end
    else if (clear_isr_running_i == 1'b1)
    begin
      // if we receive an l.rfe instruction when we are not in an
      // exception handler, we jump to the illegal instruction handler
      if (exc_running_p == 1'b1)
      begin
        // synopsys translate_off
        $display("%t: Exiting exception routine.", $time);
        // synopsys translate_on

        // the CPU should go back to sleep
        if(fetch_enable_i == 1'b0)
          exc_reason = ExcFlush;
      end
      else
        exc_reason = ExcIllegalInsn;
    end
  end

  //////////////////////////////////////////////////////////////////////
  //   _____                    _   _                ____ _        _  //
  //  | ____|_  _____ ___ _ __ | |_(_) ___  _ __    / ___| |_ _ __| | //
  //  |  _| \ \/ / __/ _ \ '_ \| __| |/ _ \| '_ \  | |   | __| '__| | //
  //  | |___ >  < (_|  __/ |_) | |_| | (_) | | | | | |___| |_| |  | | //
  //  |_____/_/\_\___\___| .__/ \__|_|\___/|_| |_|  \____|\__|_|  |_| //
  //                     |_|                                          //
  //////////////////////////////////////////////////////////////////////

  // exception control FSM
  always_comb begin
    exc_fsm_ns       = exc_fsm_cs;
    exc_reason_n     = exc_reason_p;
    exc_running_n    = exc_running_p;
    clear_exc_reason = 1'b0;
    save_pc_if_o     = 1'b0;
    save_pc_id_o     = 1'b0;
    save_sr_o        = 1'b0;
    set_dsx_o        = 1'b0;
    pipe_flushed_o   = 1'b0;
    force_nop_o      = 1'b0;
    pc_valid_o       = 1'b1;
    exc_pc_sel_o     = 1'b0;
    exc_pc_mux_o     = `EXC_PC_NO_INCR;

    case (exc_fsm_cs)
      Idle: begin
        exc_reason_n = exc_reason;

        unique case (exc_reason_n)
          // A flush of the pipeline was requested by the debug
          // unit, an l.psync instruction or an l.rfe instruction
          // execute pending delay slot (l.psync won't have one),
          // flush the pipeline and stop
          ExcDbgFlush, ExcFlush: begin
            if (jump_in_id_i == 2'b00)
            begin // no delay slot
              force_nop_o   = 1'b1;
              exc_pc_sel_o  = 1'b1;
              exc_pc_mux_o  = `EXC_PC_NO_INCR;
              pc_valid_o    = 1'b0;

              exc_fsm_ns    = NopID;
            end
            else
            begin // delay slot
              exc_fsm_ns    = NopDelay;
            end
          end

          // an IRQ is present, execute pending delay slots and jump
          // to the ISR without flushing the pipeline
          ExcIR: begin
            if (jump_in_id_i == 2'b00)
            begin // no delay slot
              // synopsys translate_off
              $display("%t: Entering exception routine.", $time);
              // synopsys translate_on

              force_nop_o      = 1'b1;
              exc_pc_sel_o     = 1'b1;
              save_pc_if_o     = 1'b1; // save current PC
              save_sr_o        = 1'b1; // save Supervision Register

              if (irq_nm_i == 1'b1) // emergency IRQ has higher priority
                exc_pc_mux_o  = `EXC_PC_IRQ_NM;
              else // irq_i == 1'b1
                exc_pc_mux_o  = `EXC_PC_IRQ;

              exc_running_n    = 1'b1;
              clear_exc_reason = 1'b1;
              exc_fsm_ns       = Idle;
            end
            else // delay slot
            begin
              exc_fsm_ns = NopDelayIR;
            end
          end

          // Illegal instruction encountered, we directly jump to
          // the ISR without flushing the pipeline
          ExcIllegalInsn: begin
            // synopsys translate_off
            $display("%t: Entering exception routine.", $time);
            // synopsys translate_on

            force_nop_o      = 1'b1;
            exc_pc_sel_o     = 1'b1;
            exc_pc_mux_o     = `EXC_PC_ILLINSN;
            save_pc_id_o     = 1'b1; // save current PC
            save_sr_o        = 1'b1; // save Supervision Register

            exc_running_n    = 1'b1;
            clear_exc_reason = 1'b1;
            exc_fsm_ns       = Idle;
          end

          // flushing pipeline because of l.trap instruction
          // we do not wait for delay slots, but we set a flag if we are in one
          ExcTrap: begin
            force_nop_o   = 1'b1;
            exc_pc_sel_o  = 1'b1;
            exc_pc_mux_o  = `EXC_PC_IRQ;
            pc_valid_o    = 1'b0;

            if (jump_in_ex_i == 2'b10)
              set_dsx_o = 1'b1; // set delay slot flag if we are in a delay slot

            exc_fsm_ns  = NopID;
          end

          // Single-step Trace Mode
          // Flush the pipeline after one instruction was executed,
          // if we are in a delay slot, wait for the delay slot to
          // be executed
          ExcST: begin
            exc_fsm_ns  = SingleStep;
          end

          default:; // Nothing
        endcase
      end // case: Idle

      // Execute exactly one instruction before stalling again
      SingleStep:
      begin
        if (jump_in_id_i == 2'b00)
        begin // no delay slot
          force_nop_o   = 1'b1;
          exc_pc_sel_o  = 1'b1;
          exc_pc_mux_o  = `EXC_PC_NO_INCR;
          pc_valid_o    = 1'b0;

          exc_fsm_ns    = NopID;
        end
        else
        begin // delay slot
          exc_fsm_ns    = NopDelay;
        end
      end

      // Execute delay slot for IR
      NopDelayIR:
      begin
        // synopsys translate_off
        $display("%t: Entering exception routine.", $time);
        // synopsys translate_on

        force_nop_o      = 1'b1;
        exc_pc_sel_o     = 1'b1;
        save_pc_if_o     = 1'b1; // save current PC
        save_sr_o        = 1'b1; // save Supervision Register

        if (irq_nm_i == 1'b1) // emergency IRQ has higher priority
          exc_pc_mux_o  = `EXC_PC_IRQ_NM;
        else // irq_i == 1'b1
          exc_pc_mux_o  = `EXC_PC_IRQ;

        exc_running_n    = 1'b1;
        clear_exc_reason = 1'b1;
        exc_fsm_ns       = Idle;
      end


      // Execute delay slot, start to force NOPs for new instructions
      NopDelay:
      begin
        force_nop_o  = 1'b1;
        exc_pc_sel_o = 1'b1;
        exc_pc_mux_o = `EXC_PC_NO_INCR;
        pc_valid_o   = 1'b0;

        exc_fsm_ns   = NopID;
      end

      // First NOP is in ID stage
      NopID:
      begin
        force_nop_o  = 1'b1;
        exc_pc_sel_o = 1'b1;
        exc_pc_mux_o = `EXC_PC_NO_INCR;
        pc_valid_o   = 1'b0;

        exc_fsm_ns   = NopEX;
      end

      // First NOP is in EX stage
      NopEX:
      begin
        force_nop_o  = 1'b1;
        pc_valid_o   = 1'b0;
        exc_pc_sel_o = 1'b1;
        exc_pc_mux_o = `EXC_PC_NO_INCR;

        exc_fsm_ns = NopWB;
      end

      // First NOP is in WB stage
      // Pipeline is flushed now
      NopWB: begin
        exc_pc_sel_o     = 1'b1;
        exc_pc_mux_o     = `EXC_PC_NO_INCR;
        pipe_flushed_o   = 1'b1;

        pc_valid_o       = 1'b0;
        force_nop_o      = 1'b1;

        clear_exc_reason = 1'b1;
        exc_fsm_ns       = Idle;
      end

      default: exc_fsm_ns = Idle;
    endcase // case (exc_fsm_cs)
  end


  always_ff @(posedge clk , negedge rst_n)
  begin : UPDATE_REGS
    if ( rst_n == 1'b0 )
    begin
      exc_fsm_cs     <= Idle;
      exc_running_p  <= 1'b0;
      exc_reason_p   <= ExcNone;
    end
    else if (stall_id_i == 1'b0)
    begin
      exc_fsm_cs     <= exc_fsm_ns;
      exc_running_p  <= (clear_isr_running_i == 1'b1) ? 1'b0    : exc_running_n;
      exc_reason_p   <= (clear_exc_reason == 1'b1)    ? ExcNone : exc_reason_n;
    end
  end

endmodule // exc_controller