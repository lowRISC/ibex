// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module gift_middle_rounds (

    // Data and key coming directly from the cipher input
    input logic [63:0]    in_data_i,
    input logic [127:0]   in_key_i,

    // Data and key coming from the state register
    input logic [63:0]    state_data_i,
    input logic [127:0]   state_key_i,

    input gift_pkg::round_index_e round_base_i,

    output logic [63:0]   data_o,
    output logic [127:0]  key_o
);

  import gift_pkg::*;

  // Internal signals

  logic [9:0][63:0] data_states;
  logic [9:0][127:0] key_states;
  logic [7:0][5:0] roundcsts;

  assign data_states[0] = state_data_i;
  assign key_states[0] = state_key_i;

  // Round constant management
  always_comb begin
    unique case (round_base_i)
      BASE_INPUT: begin
        // The first 4 rounds are not used in this case.
        for (int k = 0; k < 4; k++) begin
          roundcsts[k] = RC[4 + k];
        end
        for (int k = 0; k < 4; k++) begin
          roundcsts[k + 4] = RC[k];
        end
      end
      BASE_1: begin
        for (int k = 0; k < 8; k++) begin
          roundcsts[k] = RC[4 + k];
        end
      end
      BASE_2: begin
        for (int k = 0; k < 8; k++) begin
          roundcsts[k] = RC[12 + k];
        end
      end
      default: begin
        for (int k = 0; k < 8; k++) begin
          roundcsts[k] = RC[20 + k];
        end
      end
    endcase
  end

  // Round instantiation
  for (genvar k = 0; k < 4; k++) begin : gen_pre_inject_rounds
    gift_round gift_round_i (
        .data_i(data_states[k]),
        .key_i(key_states[k]),
        .RC_i(roundcsts[k]),

        .data_o(data_states[k+1]),
        .key_o(key_states[k+1])
    );
  end

  // Input data injection management
  always_comb begin
    unique case (round_base_i)
      BASE_INPUT: begin
        data_states[5] = in_data_i;
        key_states[5] = in_key_i;
      end
      default: begin
        data_states[5] = data_states[4];
        key_states[5] = key_states[4];
      end
    endcase
  end


  for (genvar k = 4; k < 8; k++) begin : gen_post_inject_rounds
    gift_round gift_round_i (
        .data_i(data_states[k + 1]),
        .key_i(key_states[k + 1]),
        .RC_i(roundcsts[k]),

        .data_o(data_states[k + 2]),
        .key_o(key_states[k + 2])
    );
  end

  assign data_o = data_states[9];
  assign key_o = key_states[9];

endmodule
