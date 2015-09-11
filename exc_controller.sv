////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Create Date:    20/01/2015                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    exc_controller.sv                                          //
// Project Name:   RI5CY                                                      //
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

   // Controller
   input  logic        core_busy_i,                 // Is the controller currently in the IDLE state?
   input  logic [1:0]  jump_in_id_i,                // jump instruction in ID stage
   input  logic [1:0]  jump_in_ex_i,                // jump instruction in EX stage
   input  logic        stall_id_i,                  // Stall ID stage
   input  logic        illegal_insn_i,              // Illegal instruction encountered in ID stage
   input  logic        trap_insn_i,                 // Trap instruction encountered in ID stage
   input  logic        drop_instruction_i,          // If branch prediction went wrong
   output logic        pc_valid_o,                  // is the PC in the IF stage currently valid?
   input  logic        clear_isr_running_i,         // exit ISR routine
   output logic        exc_pipe_flush_o,            // flush pipeline and go back to sleep

   // Debug Unit Signals
   input  logic        dbg_flush_pipe_i,            // Pipe flush requested
   input  logic        dbg_st_en_i,                 // Single-step trace mode enabled
   input  logic [1:0]  dbg_dsr_i,                   // Debug Stop Register
   output logic        trap_hit_o                   // Software Trap in ID (l.trap or similar stuff)
);

  // Exception unit state encoding
  enum  logic [1:0]  { ExcNone, ExcIR, ExcIllegalInsn } exc_reason;

  // Registers
  logic       exc_running_p, exc_running_n;

  // disable hardware loops when nops are inserted or the controller is not active
  assign hwloop_enable_o = (~core_busy_i);

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
  // - Debuger requests halt
  assign trap_hit_o    = trap_insn_i || dbg_flush_pipe_i || dbg_st_en_i || (illegal_insn_i && dbg_dsr_i[`DSR_IIE]) || (irq_present_o && dbg_dsr_i[`DSR_INTE] && (~exc_running_p));

  assign irq_present_o = (irq_i || irq_nm_i) && irq_enable_i;

  // Decoder for exc_reason signal
  // this signal tells the exception controller which is the exception
  // with highest priority at the moment
  // The decoder also takes care that no nested exceptions are performed
  always_comb
  begin
    exc_reason       = ExcNone;
    exc_pipe_flush_o = 1'b0;

    if (illegal_insn_i == 1'b1)
    begin
      // if the IIE bit in the Debug Stop Register is set, we transfer
      // the control to the debug interface
      // otherwise we jump to the interrupt handler, if we are not
      // already in an interrupt handler
      if ((dbg_dsr_i[`DSR_IIE] == 1'b0) && (exc_running_p == 1'b0))
        exc_reason = ExcIllegalInsn;
    end
    else if ((irq_present_o == 1'b1) && (exc_running_p == 1'b0))
    begin
      // an interrupt is present, flush pipeline, execute pending delay slots
      // and then call the interrupt handler
      // or if the INTE bit is set, transfer the control to the debug interface
      if (dbg_dsr_i[`DSR_INTE] == 1'b0)
        exc_reason = ExcIR;
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
          exc_pipe_flush_o = 1'b1;
      end
      else
        exc_reason = ExcIllegalInsn;
    end
  end

  /////////////////////////////////////////////////////////////////////
  //  _____                    _   _                ____ _        _  //
  // | ____|_  _____ ___ _ __ | |_(_) ___  _ __    / ___| |_ _ __| | //
  // |  _| \ \/ / __/ _ \ '_ \| __| |/ _ \| '_ \  | |   | __| '__| | //
  // | |___ >  < (_|  __/ |_) | |_| | (_) | | | | | |___| |_| |  | | //
  // |_____/_/\_\___\___| .__/ \__|_|\___/|_| |_|  \____|\__|_|  |_| //
  //                    |_|                                          //
  /////////////////////////////////////////////////////////////////////

  // exception control FSM
  always_comb begin
    exc_running_n    = exc_running_p;
    save_pc_if_o     = 1'b0;
    save_pc_id_o     = 1'b0;
    pc_valid_o       = 1'b1;
    exc_pc_sel_o     = 1'b0;
    exc_pc_mux_o     = `EXC_PC_NO_INCR;

    unique case (exc_reason)
      // an IRQ is present, execute pending jump and then go
      // to the ISR without flushing the pipeline
      ExcIR: begin
        if (jump_in_id_i == 2'b00 && jump_in_ex_i == 2'b00)
        begin // no jump in ID
          exc_pc_sel_o     = 1'b1;

          save_pc_if_o     = 1'b1; // save current PC

          if (irq_nm_i == 1'b1) // emergency IRQ has higher priority
            exc_pc_mux_o  = `EXC_PC_IRQ_NM;
          else // irq_i == 1'b1
            exc_pc_mux_o  = `EXC_PC_IRQ;

          exc_running_n    = 1'b1;
        end
      end

      // Illegal instruction encountered, we directly jump to
      // the ISR without flushing the pipeline
      ExcIllegalInsn: begin
        exc_pc_sel_o     = 1'b1;
        exc_pc_mux_o     = `EXC_PC_ILLINSN;
        save_pc_id_o     = 1'b1; // save current PC

        exc_running_n    = 1'b1;
      end
      default:; // Nothing
    endcase
  end


  always_ff @(posedge clk , negedge rst_n)
  begin : UPDATE_REGS
    if ( rst_n == 1'b0 )
    begin
      exc_running_p  <= 1'b0;
    end
    else
    begin
      exc_running_p  <= (clear_isr_running_i == 1'b1) ? 1'b0    : exc_running_n;
    end
  end

`ifndef SYNTHESIS
  // synopsys translate_off
  // make sure we are called later so that we do not generate messages for
  // glitches
  always_ff @(negedge clk)
  begin : EXC_DISPLAY
    if ( rst_n == 1'b1 )
    begin
      if (exc_reason != ExcNone)
        $display("%t: Entering exception routine.", $time);
    end
  end
  // synopsys translate_on
`endif

endmodule // exc_controller
