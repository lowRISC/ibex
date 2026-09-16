// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Formal testbench for ibex_branch_predict.
// This gets instantiated inside the DUT via formal_tb_frag.svh.

`include "prim_assert.sv"

`define IMPLIES(a, b) ((b) || (!(a)))

module formal_tb 
    import ibex_pkg::*;
(
  input logic        clk_i,
  input logic        rst_ni,

  input logic [31:0] fetch_rdata_i,
  input logic [31:0] fetch_pc_i,
  input logic        fetch_valid_i,

  input logic        predict_branch_taken_o,
  input logic [31:0] predict_branch_pc_o
);

logic f_is_jal;
logic f_is_branch;
logic f_is_cb;
logic f_is_cj;


//branch types 
assign f_is_cj = (fetch_rdata_i[1:0] == 2'b01) & ((fetch_rdata_i[15:13] == 3'b101) | (fetch_rdata_i[15:13] == 3'b001));

assign f_is_cb = (fetch_rdata_i[1:0] == 2'b01) & ((fetch_rdata_i[15:13] == 3'b110) | (fetch_rdata_i[15:13] == 3'b111));

assign f_is_jal = opcode_e'(fetch_rdata_i[6:0]) == OPCODE_JAL;

assign f_is_branch =opcode_e'(fetch_rdata_i[6:0]) == OPCODE_BRANCH;



logic [31:0] f_j_imm;
logic [31:0] f_b_imm;
logic [31:0] f_cj_imm;
logic [31:0] f_cb_imm;

//immediates for target calculations 
assign f_j_imm = { {12{fetch_rdata_i[31]}}, fetch_rdata_i[19:12], fetch_rdata_i[20], fetch_rdata_i[30:21], 1'b0 };
assign f_b_imm = { {19{fetch_rdata_i[31]}}, fetch_rdata_i[31], fetch_rdata_i[7], fetch_rdata_i[30:25],fetch_rdata_i[11:8], 1'b0 };
assign f_cj_imm = {{20{fetch_rdata_i[12]}},fetch_rdata_i[12],fetch_rdata_i[8],
  fetch_rdata_i[10:9],fetch_rdata_i[6],fetch_rdata_i[7],fetch_rdata_i[2], fetch_rdata_i[11],fetch_rdata_i[5:3], 1'b0
};
assign f_cb_imm = {
  {23{fetch_rdata_i[12]}},fetch_rdata_i[12],fetch_rdata_i[6:5],fetch_rdata_i[2],fetch_rdata_i[11:10],fetch_rdata_i[4:3],1'b0
};


// Reference ("golden-model") signals: an independent decode of what the DUT should predict,
// built the same way ibex_branch_predict itself picks a taken/not-taken result and an immediate
// per instruction type. Comparing against these with `==` lets one assertion stand in for the
// not-valid / not-a-branch / positive / negative cases all at once, instead of an implication
// per case.
logic        f_taken_ref;
logic [31:0] f_imm_ref;

assign f_taken_ref = fetch_valid_i &&
                     (f_is_jal || f_is_cj ||
                      (f_is_branch && fetch_rdata_i[31]) ||
                      (f_is_cb    && fetch_rdata_i[12]));

always_comb begin
  unique case (1'b1)
    f_is_jal:    f_imm_ref = f_j_imm;
    f_is_branch: f_imm_ref = f_b_imm;
    f_is_cj:     f_imm_ref = f_cj_imm;
    f_is_cb:     f_imm_ref = f_cb_imm;
    default:     f_imm_ref = f_b_imm;  // don't-care: gated off by predict_target_matches_ref below
  endcase
end

// predict_branch_taken_o exactly matches "unconditional jump, or a conditional branch whose
// offset is negative". Subsumes jal_taken/no_prediction_when_invalid/no_prediction_not_branch/
// neg_b_taken/pos_b_not_taken/comp_jal_taken/comp_neg_b_taken/comp_pos_b_not_taken.
`ASSERT(predict_taken_matches_ref, predict_branch_taken_o == f_taken_ref)

// predict_branch_pc_o is always fetch_pc_i + the immediate for whichever type was decoded --
// the DUT computes this unconditionally, even when the prediction itself is not-taken.
`ASSERT(predict_target_matches_ref,
        `IMPLIES(fetch_valid_i && (f_is_jal || f_is_branch || f_is_cj || f_is_cb),
                 predict_branch_pc_o == fetch_pc_i + f_imm_ref))


//check for valid JAL 
`COVER(jal_reachable,
        fetch_valid_i && f_is_jal)

//valid compressed jump 
`COVER(cj_reachable,
       fetch_valid_i && f_is_cj)

//negative branch reached
`COVER(neg_branch_reachable,
       fetch_valid_i &&
       f_is_branch &&
       fetch_rdata_i[31])

//positive branch reachable 
`COVER(pos_branch_reachable,
       fetch_valid_i &&
       f_is_branch &&
       !fetch_rdata_i[31])

//negative compressed branch 
`COVER(neg_cb_reachable,
       fetch_valid_i &&
       f_is_cb &&
       fetch_rdata_i[12])

//positive compressed branch 
`COVER(pos_cb_reachable,
       fetch_valid_i &&
       f_is_cb &&
       !fetch_rdata_i[12])

endmodule