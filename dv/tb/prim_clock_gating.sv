// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Dummy clock gating module

module prim_clock_gating #(
    parameter Impl = "default"
) (
    input        clk_i,
    input        en_i,
    input        test_en_i,
    output logic clk_o
);

  assign clk_o = en_i ? clk_i : 0;

endmodule
