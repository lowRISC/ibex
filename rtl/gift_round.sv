// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module gift_round (
    input   logic [63:0]  data_i,
    input   logic [127:0] key_i,
    input   logic [5:0]   RC_i, // RC[RoundIndex]

    output  logic [63:0]  data_o,
    output  logic [127:0] key_o
);

  import gift_pkg::*;

  logic [63:0] data_after_sbox;
  logic [63:0] data_after_permut;
  logic [63:0] data_after_key;

  // Avoid lint warning
  logic [63:0] unused_data_after_permut;
  logic [63:0] unused_data_after_key;

  gift_update_key i_gift_update_key (
    .key_i(key_i),
    .key_o(key_o)
  );

  logic [63:0] data_state;

  always_comb begin : p_gift_round

    data_state = data_i;

    data_state = sbox_layer(data_state);

    data_after_sbox = data_state;

    data_state = permut_layer(data_after_sbox);

    data_after_permut = data_state;

    // Add round key

    for (int k = 0; k < 16; k++) begin
      data_state[4 * k] ^= key_i[k];
      data_state[4 * k + 1] ^= key_i[k + 16];
    end

    data_after_key = data_state;

    // Add round constant

    data_state[63] ^= 1;
    data_state[23] ^= RC_i[5];
    data_state[19] ^= RC_i[4];
    data_state[15] ^= RC_i[3];
    data_state[11] ^= RC_i[2];
    data_state[7] ^= RC_i[1];
    data_state[3] ^= RC_i[0];

  end

  assign data_o = data_state;

  // Avoid lint warning
  assign unused_data_after_permut = data_after_permut;
  assign unused_data_after_key    = data_after_key;

endmodule
