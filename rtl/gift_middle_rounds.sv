// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import gift_pkg::*;

module gift_middle_rounds (
    input logic [63:0]    data_i,
    input logic [127:0]   key_i,

    input round_index_e    round_base_i,

    output logic [63:0]   data_o,
    output logic [127:0]  key_o
);


  // Internal signals

  logic [9:0][63:0] data_states;
  logic [9:0][127:0] key_states;
  logic [8:0][5:0] roundcsts;

  assign data_states[0] = data_i;
  assign key_states[0] = key_i;

  // Round constant management
  always_comb begin
    unique case (round_base_i)
      BASE_1: begin
        for (int k = 0; k < 9; k++) begin
          roundcsts[k] = RC[k];
        end
      end
      BASE_2: begin
        for (int k = 0; k < 9; k++) begin
          roundcsts[k] = RC[9 + k];
        end
      end
      default: begin
        for (int k = 0; k < 9; k++) begin
          roundcsts[k] = RC[18 + k];
        end
      end
    endcase
  end

  // Round instantiation
  for (genvar i = 0; i < 9; i++) begin : gen_rounds
    gift_round gift_round_i (
        .data_i(data_states[i]),
        .key_i(key_states[i]),
        .RC_i(roundcsts[i]),

        .data_o(data_states[i+1]),
        .key_o(key_states[i+1])
    );
  end

  assign data_o = data_states[9];
  assign key_o = key_states[9];

endmodule
