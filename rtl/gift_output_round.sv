module gift_output_round (
  input   logic [63:0]  data_i,
  input   logic [127:0] key_i,

  output  logic [63:0]  data_o
);

  import gift_pkg::*;

  logic [63:0] data_after_sbox;
  logic [63:0] data_after_permut;
  logic [63:0] data_after_key;

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
    data_state[23] ^= RC[27][5];
    data_state[19] ^= RC[27][4];
    data_state[15] ^= RC[27][3];
    data_state[11] ^= RC[27][2];
    data_state[7] ^= RC[27][1];
    data_state[3] ^= RC[27][0];

  end

  assign data_o = data_state;

endmodule
