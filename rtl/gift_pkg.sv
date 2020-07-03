// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package gift_pkg;

  localparam logic [3:0] GSBOX[16] = {
    4'h1, 4'hA, 4'h4, 4'hC, 4'h6, 4'hF, 4'h3, 4'h9, 4'h2, 4'hD, 4'hB, 4'h7, 4'h5, 4'h0, 4'h8, 4'hE
  };

  localparam logic [5:0] P_PERMUT[64] = {
    6'd0, 6'd17, 6'd34, 6'd51, 6'd48, 6'd1, 6'd18, 6'd35, 6'd32, 6'd49, 6'd2, 6'd19, 6'd16, 6'd33,
    6'd50, 6'd3, 6'd4, 6'd21, 6'd38, 6'd55, 6'd52, 6'd5, 6'd22, 6'd39, 6'd36, 6'd53, 6'd6, 6'd23,
    6'd20, 6'd37, 6'd54, 6'd7, 6'd8, 6'd25, 6'd42, 6'd59, 6'd56, 6'd9, 6'd26, 6'd43, 6'd40, 6'd57,
    6'd10, 6'd27, 6'd24, 6'd41, 6'd58, 6'd11, 6'd12, 6'd29, 6'd46, 6'd63, 6'd60, 6'd13, 6'd30,
    6'd47, 6'd44, 6'd61, 6'd14, 6'd31, 6'd28, 6'd45, 6'd62, 6'd15
  };

  localparam logic [31:0][5:0] RC = {
    6'h0B, 6'h05, 6'h02, 6'h21, 6'h30, 6'h18, 6'h2C, 6'h16, 6'h2B, 6'h35, 6'h3A, 6'h1D, 6'h0E,
    6'h27, 6'h33, 6'h39, 6'h3C, 6'h1E, 6'h2F, 6'h37, 6'h3B, 6'h3D, 6'h3E, 6'h1F, 6'h0F, 6'h07,
    6'h03, 6'h01
  };

  typedef enum logic [1:0] {
    BASE_INPUT,
    BASE_1,
    BASE_2,
    BASE_3
  } round_index_e;

  typedef enum logic {
    ROUND_FWD,
    ROUND_INV
  } round_op_e;

  function automatic logic [15:0] rot_right_16_2(logic [15:0] data_in);
    logic [15:0] data_out;
    for (int k = 0; k < 14; k++) begin
      data_out[k] = data_in[k+2];
    end

    data_out[14] = data_in[0];
    data_out[15] = data_in[1];

    return data_out;
  endfunction : rot_right_16_2

  function automatic logic [15:0] rot_right_16_12(logic [15:0] data_in);
    logic [15:0] data_out;
    for (int k = 0; k < 4; k++) begin
      data_out[k] = data_in[k+12];
    end

    for (int k = 0; k < 12; k++) begin
      data_out[k+4] = data_in[k];
    end

    return data_out;
  endfunction : rot_right_16_12

  function automatic logic [63:0] sbox_layer(logic [63:0] state_in);
    logic [63:0] state_out;
    for (int k = 0; k < 16; k++) begin
      state_out[k * 4 +: 4] = GSBOX[state_in[k * 4 +: 4]];
    end
    return state_out;
  endfunction : sbox_layer

  function automatic logic [63:0] permut_layer(logic [63:0] state_in);
    logic [63:0] state_out;
    for (int k = 0; k < 64; k++) begin
      state_out[P_PERMUT[k]] = state_in[k];
    end
    return state_out;
  endfunction : permut_layer

endpackage : gift_pkg
