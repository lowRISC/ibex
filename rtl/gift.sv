// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module gift (
  input logic clk_i,
  input logic rst_ni,

  input logic out_ready_i,
  input logic in_valid_i,

  input logic [63:0] data_i,
  input logic [127:0] key_i,

  output logic in_ready_o,
  output logic out_valid_o,

  output logic [63:0] data_o
);

  import gift_pkg::*;

  typedef enum logic [2:0]{
    ROUNDS_INPUT,
    ROUNDS_INTERNAL_1,
    ROUNDS_INTERNAL_2,
    ROUNDS_INTERNAL_3,
    ROUNDS_OUTPUT
  } state_e;

  // Sequential signal declaration
  state_e state_d, state_q;
  logic [63:0] data_d, data_q;
  logic [127:0] key_d, key_q;

  // Write enable signal declaration
  logic data_we, key_we;

  // Inter-module signal declaration
  logic [63:0] data_after_middle_rounds;
  logic [127:0] key_after_middle_rounds;

  round_index_e current_round_base;

  //  Middle and output modules instantiation
  gift_middle_rounds gift_middle_rounds_i (
    .data_i(data_q),
    .key_i(key_q),

    .round_base_i(current_round_base),

    .data_o(data_after_middle_rounds),
    .key_o(key_after_middle_rounds)
  );

  gift_output_round gift_output_round_i (
    .data_i(data_q),
    .key_i(key_q),

    .data_o(data_o)
  );

  // Flip-flop
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_q <= 64'b0;
    end else if (data_we) begin
      data_q <= data_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      key_q <= 128'b0;
    end else if (key_we) begin
      key_q <= key_d;
    end
  end

  // FSM
  always_comb begin : gift_cipher_fsm

    // Key management
    key_we = 1'b0;
    key_d = key_q;

    // Data write enable
    data_we = 1'b0;

    // Stored signals, arbitrarily set by default to the rectangle output
    data_d = data_q;

    // Gift rectangle-specific signals
    current_round_base = BASE_1;

    // Handshake signals
    in_ready_o = 1'b0;
    out_valid_o = 1'b0;

    // State partitioning
    unique case (state_q)

      ROUNDS_INPUT: begin

        // Take the new key, tweak and data into account
        key_we = 1'b1;
        key_d = key_i;

        data_we = 1'b1;
        data_d = data_i;

        // In this state, the cipher is ready to get data
        in_ready_o = 1'b1;

        // If the handshake takes place, then proceed to the next state
        if (in_valid_i) begin
          state_d = ROUNDS_INTERNAL_1;
        end else begin
          state_d = ROUNDS_INPUT;
        end
      end

      ROUNDS_INTERNAL_1: begin

        // Key update

        key_we = 1'b1;
        key_d = key_after_middle_rounds;

        data_we = 1'b1;

        // Take middle rounds outputs into account
        data_d = data_after_middle_rounds;

        // Gift rectangle-specific signals
        current_round_base = BASE_1;

        // State transition
        state_d = ROUNDS_INTERNAL_2;
      end

      ROUNDS_INTERNAL_2: begin

        // Key update
        key_we = 1'b1;
        key_d = key_after_middle_rounds;

        data_we = 1'b1;

        // Take middle rounds outputs into account
        data_d = data_after_middle_rounds;

        // Gift rectangle-specific signals
        current_round_base = BASE_2;

        // State transition
        state_d = ROUNDS_INTERNAL_3;
      end

      ROUNDS_INTERNAL_3: begin

        // Key update
        key_we = 1'b1;
        key_d = key_after_middle_rounds;

        data_we = 1'b1;

        // Take middle rounds outputs into account
        data_d = data_after_middle_rounds;

        // Gift rectangle-specific signals
        current_round_base = BASE_3;

        // State transition
        state_d = ROUNDS_OUTPUT;
      end

      ROUNDS_OUTPUT: begin

        // In this state, the cipher output data is valid
        out_valid_o = 1'b1;

        // Handshake-dependent state update and register input
        if (!out_ready_i) begin
          // Select register input

          key_we = 1'b0;
          data_we = 1'b0;

          // State transition
          state_d = ROUNDS_OUTPUT;

        end else begin

          in_ready_o = 1'b1;

          if (in_valid_i) begin
            // Select register input
            key_we = 1'b1;
            data_we = 1'b1;

            data_d = data_i;
            key_d = key_i;

            // State transition
            state_d = ROUNDS_INTERNAL_1;

          end else begin
            // Register input does not matter, keep its value
            key_we = 1'b0;
            data_we = 1'b0;

            // State transition
            state_d = ROUNDS_INPUT;
          end
        end
      end

      default: begin
        state_d = ROUNDS_INPUT;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= ROUNDS_INPUT;
    end else begin
      state_q <= state_d;
    end
  end

endmodule
