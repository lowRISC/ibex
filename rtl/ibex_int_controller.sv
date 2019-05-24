// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
// Design Name:    Interrupt Controller                                       //
// Project Name:   ibex                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Interrupt Controller of the pipelined processor            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

/**
 * Interrupt Controller
 */
module ibex_int_controller (
    input  logic        clk_i,
    input  logic        rst_ni,

    // irq_req for controller
    output logic        irq_req_ctrl_o,
    output logic  [4:0] irq_id_ctrl_o,

    // handshake signals to controller
    input  logic        ctrl_ack_i,
    input  logic        ctrl_kill_i,

    // external interrupt lines
    input  logic        irq_i,          // level-triggered interrupt inputs
    input  logic  [4:0] irq_id_i,       // interrupt id [0,1,....31]

    input  logic        m_IE_i          // interrupt enable bit from CSR (M mode)
);

  import ibex_defines::*;

  typedef enum logic [1:0] { IDLE, IRQ_PENDING, IRQ_DONE} exc_ctrl_e;
  exc_ctrl_e exc_ctrl_ns, exc_ctrl_cs;

  logic irq_enable_ext;
  logic [4:0] irq_id_d, irq_id_q;

  assign irq_enable_ext =  m_IE_i;
  assign irq_req_ctrl_o = exc_ctrl_cs == IRQ_PENDING;
  assign irq_id_ctrl_o  = irq_id_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      irq_id_q    <= '0;
      exc_ctrl_cs <= IDLE;
    end else begin
      irq_id_q    <= irq_id_d;
      exc_ctrl_cs <= exc_ctrl_ns;
    end
  end

  always_comb begin
    irq_id_d = irq_id_q;
    exc_ctrl_ns = exc_ctrl_cs;
    unique case (exc_ctrl_cs)
      IDLE: begin
        if (irq_enable_ext && irq_i) begin
          exc_ctrl_ns = IRQ_PENDING;
          irq_id_d    = irq_id_i;
        end
      end

      IRQ_PENDING: begin
        unique case(1'b1)
          ctrl_ack_i:
            exc_ctrl_ns = IRQ_DONE;
          ctrl_kill_i:
            exc_ctrl_ns = IDLE;
          default:
            exc_ctrl_ns = IRQ_PENDING;
        endcase
      end

      IRQ_DONE: begin
        exc_ctrl_ns = IDLE;
      end

      default: begin
        exc_ctrl_ns = exc_ctrl_e'(1'bX);
      end
    endcase
  end

endmodule
