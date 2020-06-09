// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is just a placeholder for the actual cipher core that will be connected later.
module ibex_cipher (
  input  logic         clk_i,
  input  logic         rst_ni,

  input  logic [127:0] key_i,

  input  logic [63:0]  in_data_i,
  input  logic         in_valid_i,
  output  logic        in_ready_o,

  output logic [31:0]  out_data_o,
  output logic         out_valid_o,
  input  logic         out_ready_i
);

  logic [127:0] key_q, key_d;
  logic [63:0]  data_q, data_d;

  typedef enum logic [2:0] {
    C_INPUT, C_CALC1, C_CALC2, C_CALC3, C_OUTPUT
  } c_fsm_e;
  c_fsm_e c_fsm_q, c_fsm_d;

  always_comb begin
    key_d       = key_q;
    data_d      = data_q;
    in_ready_o  = '0;
    out_data_o  = '0;
    out_valid_o = '0;
    c_fsm_d     = c_fsm_q;

    unique case (c_fsm_q)

      C_INPUT: begin
        in_ready_o = 1'b1;
        if (in_valid_i) begin
          data_d  = in_data_i;
          key_d   = key_i;
          c_fsm_d = C_CALC1;
        end
      end

      C_CALC1: begin
        data_d = key_q[63:0] ^ data_q; // placeholder calculation
        c_fsm_d = C_CALC2;
      end
      C_CALC2: begin
        data_d = key_q[127:64] ^ data_q; // placeholder calculation
        c_fsm_d = C_CALC3;
      end
      C_CALC3: begin
        data_d = key_q[63:0] ^ data_q; // placeholder calculation
        c_fsm_d = C_OUTPUT;
      end

      C_OUTPUT: begin
        if (out_ready_i) begin
          out_data_o  = data_q[31:0] ^ data_q[63:32];
          out_valid_o = 1'b1;
          c_fsm_d     = C_INPUT;
        end
      end

      default: begin
        c_fsm_d = C_INPUT;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      c_fsm_q <= C_INPUT;
      key_q   <= '0;
      data_q  <= '0;
    end else begin
      c_fsm_q <= c_fsm_d;
      key_q   <= key_d;
      data_q  <= data_d;
    end
  end

endmodule
