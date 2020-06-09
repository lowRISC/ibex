// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module gift_update_key (
    input   logic [127:0] key_i,
    output  logic [127:0] key_o
);

  import gift_pkg::*;

  assign key_o[1 * 16 - 1 : 0 * 16] = key_i[3 * 16 - 1 : 2 * 16];
  assign key_o[2 * 16 - 1 : 1 * 16] = key_i[4 * 16 - 1 : 3 * 16];
  assign key_o[3 * 16 - 1 : 2 * 16] = key_i[5 * 16 - 1 : 4 * 16];
  assign key_o[4 * 16 - 1 : 3 * 16] = key_i[6 * 16 - 1 : 5 * 16];
  assign key_o[5 * 16 - 1 : 4 * 16] = key_i[7 * 16 - 1 : 6 * 16];
  assign key_o[6 * 16 - 1 : 5 * 16] = key_i[8 * 16 - 1 : 7 * 16];

  assign key_o[7 * 16 - 1 : 6 * 16] = rot_right_16_12(key_i[1 * 16 - 1 : 0]);
  assign key_o[8 * 16 - 1 : 7 * 16] = rot_right_16_2(key_i[2 * 16 - 1 : 1 * 16]);

endmodule
