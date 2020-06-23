// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A formal testbench for the ICache. This gets bound into the actual ICache DUT.

`include "prim_assert.sv"

// A macro to emulate |-> (a syntax that Yosys doesn't currently support).
`define IMPLIES(a, b) ((b) || (!(a)))

module formal_tb #(
  // DUT parameters
  parameter int unsigned BusWidth       = 32,
  parameter int unsigned CacheSizeBytes = 4*1024,
  parameter bit          ICacheECC      = 1'b0,
  parameter int unsigned LineSize       = 64,
  parameter int unsigned NumWays        = 2,
  parameter bit          SpecRequest    = 1'b0,
  parameter bit          BranchCache    = 1'b0,

  // Internal parameters / localparams
  parameter int unsigned NUM_FB         = 4
) (
   // Top-level ports
   input logic                          clk_i,
   input logic                          rst_ni,
   input logic                          req_i,
   input logic                          branch_i,
   input logic                          branch_spec_i,
   input logic [31:0]                   addr_i,
   input logic                          ready_i,
   input logic                          valid_o,
   input logic [31:0]                   rdata_o,
   input logic [31:0]                   addr_o,
   input logic                          err_o,
   input logic                          err_plus2_o,
   input logic                          instr_req_o,
   input logic                          instr_gnt_i,
   input logic [31:0]                   instr_addr_o,
   input logic [BusWidth-1:0]           instr_rdata_i,
   input logic                          instr_err_i,
   input logic                          instr_pmp_err_i,
   input logic                          instr_rvalid_i,
   input logic                          icache_enable_i,
   input logic                          icache_inval_i,
   input logic                          busy_o,

   // Internal signals
   input logic [NUM_FB-1:0]             fill_busy_q,
   input logic [NUM_FB-1:0][NUM_FB-1:0] fill_older_q
);

  // We are bound into the DUT. This means we don't control the clock and reset directly, but we
  // still want to constrain rst_ni to reset the module at the start of time (for one cycle) and
  // then stay high.
  //
  // Note that having a cycle with rst_ni low at the start of time means that we can safely use
  // $past, $rose and $fell in calls to `ASSERT without any need for an "f_past_valid signal": they
  // will only be evaluated from cycle 2 onwards.
  logic [1:0] f_startup_count = 2'd0;
  always_ff @(posedge clk_i) begin : reset_assertion
    f_startup_count <= f_startup_count + ((f_startup_count == 2'd3) ? 2'd0 : 2'd1);

    // Assume that rst_ni is low for the first cycle and not true after that.
    assume (~((f_startup_count == 2'd0) ^ ~rst_ni));

    // There is a feed-through path from branch_i to req_o which isn't squashed when in reset. Assume
    // that branch_i isn't asserted when in reset.
    assume (`IMPLIES(!rst_ni, !branch_i));
  end

  // Top-level assertions
  //
  // This section contains the assertions that prove the properties we care about. All should be
  // about observable signals (so shouldn't contain any references to anything that isn't exposed as
  // an input port).

  //  REQ stays high until GNT
  //
  //  If instr_req_o goes high, we won't drive it low again until instr_gnt_i or instr_pmp_err_i is
  //  high (the latter signals that the outgoing request got squashed, so we can forget about it).
  //
  //  Read this as "a negedge of instr_req_o implies that the transaction was granted or squashed on
  //  the previous cycle".
  `ASSERT(req_to_gnt,
          `IMPLIES($fell(instr_req_o), $past(instr_gnt_i | instr_pmp_err_i)))

  //  ADDR stability
  //
  //  If instr_req_o goes high, the address at instr_addr_o will stay constant until the request is
  //  squashed or granted. The encoding below says "either the address is stable, the request has
  //  been squashed, we've had a grant or this is a new request".
  `ASSERT(req_addr_stable,
          $stable(instr_addr_o) | $past(instr_gnt_i | instr_pmp_err_i | ~instr_req_o))


  // Internal (induction) assertions
  //
  // Code below this line can refer to internal signals of the DUT. The assertions shouldn't be
  // needed for BMC checks, but will be required to constrain the state space used for k-induction.

  for (genvar fb = 0; fb < NUM_FB; fb++) begin : g_fb_older_asserts
    // If fill buffer i is busy then fill_older_q[i][j] means that that fill buffer j has an
    // outstanding request which started before us (and should take precedence). We should check
    // that this only happens if buffer j is indeed busy.
    //
    //   fill_busy_q[i] -> fill_older_q[i][j] -> fill_busy_q[j]
    //
    // which we can encode as
    //
    //   (fill_older_q[i][j] -> fill_busy_q[j]) | ~fill_busy_q[i]
    //    = (fill_busy_q[j] | ~fill_older_q[i][j]) | ~fill_busy_q[i]
    //
    // Grouping by j, we can rewrite this as:
    `ASSERT(older_is_busy, &(fill_busy_q | ~fill_older_q[fb]) | ~fill_busy_q[fb])

    // No fill buffer should ever think that it's older than itself
    `ASSERT(older_anti_refl, !fill_older_q[fb][fb])

    // The "older" relation should be anti-symmetric (a fill buffer can't be both older than, and
    // younger than, another). This takes NUM_FB*(NUM_FB-1)/2 assertions, comparing each pair of
    // buffers. Here, we do this by looping over the indices below fb.
    //
    // If I and J both think the other is older, then fill_older_q[I][J] and fill_older_q[J][I] will
    // both be true. Check that doesn't happen.
    for (genvar fb2 = 0; fb2 < fb; fb2++) begin : g_older_anti_symm_asserts
      `ASSERT(older_anti_symm, ~(fill_older_q[fb][fb2] & fill_older_q[fb2][fb]))
    end

    // The older relation should be transitive (if i is older than j and j is older than k, then i
    // is older than k). That is:
    //
    //   (fill_busy_q[i] & fill_older_q[i][j]) ->
    //   (fill_busy_q[j] & fill_older_q[j][k]) ->
    //   (fill_busy_q[i] & fill_older_q[i][k])
    //
    // Note that the second fill_busy_q[i] holds trivially and fill_busy_q[j] holds because of
    // order_is_busy, so this can be rewritten as:
    //
    //   fill_busy_q[i] & fill_older_q[i][j] -> fill_older_q[j][k] -> fill_older_q[i][k]
    //
    // Converting A->B->C into (A&B)->C and then rewriting A->B as B|~A, this is equivalent to
    //
    //   (fill_older_q[i][k] | ~fill_older_q[j][k]) | ~(fill_busy_q[i] & fill_older_q[i][j])
    //
    // Looping over i and j, we can simplify this as
    //
    //   &(fill_older_q[i] | ~fill_older_q[j]) | ~(fill_busy_q[i] & fill_older_q[i][j])
    //
    for (genvar fb2 = 0; fb2 < NUM_FB; fb2++) begin : g_older_transitive_asserts
      `ASSERT(older_transitive,
              (&(fill_older_q[fb] | ~fill_older_q[fb2]) |
               ~(fill_busy_q[fb] & fill_older_q[fb][fb2])))
    end

    // The older relation should be total. This is a bit finicky because of fill buffers that aren't
    // currently busy. Specifically, we want
    //
    //   i != j -> fill_busy_q[i] -> fill_busy_q[j] -> (fill_older_q[i][j] | fill_older_q[j][i])
    //
    for (genvar fb2 = 0; fb2 < fb; fb2++) begin : g_older_total_asserts
      `ASSERT(older_total,
              `IMPLIES(fill_busy_q[fb] & fill_busy_q[fb2],
                       fill_older_q[fb][fb2] | fill_older_q[fb2][fb]))
    end
  end

endmodule
