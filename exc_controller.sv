////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Andreas Traber - atraber@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
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
////////////////////////////////////////////////////////////////////////////////

`include "defines.sv"


module riscv_exc_controller
(
  input  logic        clk,
  input  logic        rst_n,

  // handshake signals to controller
  output logic        req_o,
  input  logic        ack_i,

  // to IF stage
  output logic  [1:0] pc_mux_o,       // selects target PC for exception
  output logic  [4:0] vec_pc_mux_o,   // selects interrupt handler for vectorized interrupts

  // interrupt lines
  input  logic [31:0] irq_i,          // level-triggered interrupt inputs
  input  logic        irq_enable_i,   // interrupt enable bit from CSR

  // from decoder
  input  logic        illegal_insn_i, // illegal instruction encountered
  input  logic        ecall_insn_i,   // ecall instruction encountered
  input  logic        eret_insn_i,    // eret instruction encountered

  // to CSR
  output logic [5:0]  cause_o,
  output logic        save_cause_o
);


  enum logic [1:0] { IDLE, WAIT_CONTROLLER, IN_ISR } exc_ctrl_cs, exc_ctrl_ns;

  logic req_int;
  logic [1:0] pc_mux_int, pc_mux_int_d;
  logic [5:0] cause_int, cause_int_d;

  integer i;


  assign req_int = illegal_insn_i | ecall_insn_i | (irq_enable_i & (|irq_i));


  // Exception cause and ISR address selection
  always_comb
  begin
    cause_int  = 6'b0;
    pc_mux_int = 2'b0;

    for (i = 31; i >= 0; i--)
    begin
      if (irq_enable_i && irq_i[i]) begin
        cause_int[5]   = 1'b1;
        cause_int[4:0] = i;
        pc_mux_int     = `EXC_PC_IRQ;
      end
    end

    if (ecall_insn_i) begin
      cause_int  = 6'b0_01000;
      pc_mux_int = `EXC_PC_ECALL;
    end

    if (illegal_insn_i) begin
      cause_int  = 6'b0_00010;
      pc_mux_int = `EXC_PC_ILLINSN;
    end
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      cause_int_d  <= '0;
      pc_mux_int_d <= '0;
    end else if (exc_ctrl_cs == IDLE && req_int) begin
      // save cause and ISR when new irq request is first sent to controller
      cause_int_d  <= cause_int;
      pc_mux_int_d <= pc_mux_int;
    end
  end


  // Exception cause and mux output (with bypass)
  assign cause_o      = (exc_ctrl_cs == IDLE && req_int)? cause_int  : cause_int_d;
  assign pc_mux_o     = (exc_ctrl_cs == IDLE && req_int)? pc_mux_int : pc_mux_int_d;

  assign vec_pc_mux_o = (cause_o[5] == 1'b1)? cause_o[4:0] : 5'b0;


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

        if (req_int)
          exc_ctrl_ns = WAIT_CONTROLLER;
      end

      WAIT_CONTROLLER:
      begin
        req_o = 1'b1;

        if (ack_i) begin
          save_cause_o = 1'b1;
          exc_ctrl_ns  = IN_ISR;
        end
      end

      IN_ISR:
      begin
        if (eret_insn_i)
          exc_ctrl_ns = IDLE;
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
