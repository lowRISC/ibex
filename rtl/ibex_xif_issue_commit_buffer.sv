// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * XInterface Issue-Commit Buffer
 *
 * Issue-Commit Buffer: Register the information of issued and committed instructions.
 * Decide whether to commit a new instruction and generate commit signals.
 */

`include "prim_assert.sv"

module ibex_xif_issue_commit_buffer import ibex_pkg::*; #(
  parameter int unsigned IdWidth = X_ID_WIDTH - 1
) (
  input  logic                  clk_i,
  input  logic                  rst_ni,

  // reset all issued and not committed instructions
  input  logic                  exc_rst_i,

  // issue interface
  output logic [X_ID_WIDTH-1:0] issue_id_o,
  output logic                  issue_id_valid_o,
  input  logic                  issue_accept_i,
  input  logic                  issue_wb_i,
  input  logic                  issue_ls_i,
  input  logic                  issue_ecsw_i,
  input  logic                  issue_exc_i,

  // cpu task stall because of outstanding external instructions ocuppying id/ex stage
  output logic                  stall_external_o,

  // commit interface
  output logic                  commit_valid_o,
  output logic [X_ID_WIDTH-1:0] commit_id_o,
  output logic                  commit_kill_o,

  // memory interface
  input  logic [X_ID_WIDTH-1:0] mem_id_i,
  output logic                  mem_commit_o,

  // memory result interface
  input  logic                  mem_result_fin_i,
  input  logic [X_ID_WIDTH-1:0] mem_result_id_i,

  // result interface
  input  logic                  result_fin_i,
  input  logic [X_ID_WIDTH-1:0] result_id_i
);

  localparam int unsigned BufferEntries = 2**IdWidth;

  logic [BufferEntries-1:0] valid_d, valid_q;
  logic [BufferEntries-1:0] writeback_d, writeback_q;
  logic [BufferEntries-1:0] loadstore_d, loadstore_q;
  logic [BufferEntries-1:0] ecswrite_d, ecswrite_q;
  logic [BufferEntries-1:0] exc_d, exc_q;

  logic [IdWidth-1:0] issue_id_d, issue_id_q;
  logic [IdWidth-1:0] commit_id_d, commit_id_q;

  logic [IdWidth-1:0] mem_id_low;
  logic [IdWidth-1:0] mem_result_id_low;
  logic [IdWidth-1:0] result_id_low;

  logic [X_ID_WIDTH-IdWidth-1:0] unsued_mem_id_high;
  logic [X_ID_WIDTH-IdWidth-1:0] unused_mem_result_id_high;
  logic [X_ID_WIDTH-IdWidth-1:0] unused_result_id_high;

  logic all_committed;
  logic commit_ready;

  assign mem_id_low        = mem_id_i[IdWidth-1:0];
  assign mem_result_id_low = mem_result_id_i[IdWidth-1:0];
  assign result_id_low     = result_id_i[IdWidth-1:0];

  assign unsued_mem_id_high        = mem_id_i[X_ID_WIDTH-1:IdWidth];
  assign unsued_mem_result_id_high = mem_result_id_i[X_ID_WIDTH-1:IdWidth];
  assign unsued_result_id_high     = result_id_i[X_ID_WIDTH-1:IdWidth];

  assign issue_id_o       = {{X_ID_WIDTH-IdWidth{1'b0}}, issue_id_q};
  assign issue_id_valid_o = ~valid_d[result_id_q];

  // All instructions are committed when the two pointers points to the same position.
  assign all_committed  = (commit_id_q == issue_id_q);
  // Ready to commit a new instruction when:
  // 1.The last instruction has been completed, or
  // 2.The last instruction will not:
  //   a) writeback, or
  //   b) use lsu, or
  //   c) write into extension context status, or
  //   d) raise an exception
  assign commit_ready   = ~valid[commit_id_q-1] |
                          ~(writeback_q[commit_id_q-1] | loadstore_q[commit_id_q-1] |
                            ecswrite_q[commit_id_q-1] | exc_q[commit_id_q-1]);
  assign commit_valid_o = commit_ready & ~all_committed;
  assign commit_kill_o  = commit_valid_o;
  assign commit_id_d    = commit_valid_o ? commit_id_q + 1 : commit_id_q;
  assign commit_id_o    = {{X_ID_WIDTH-IdWidth{1'b0}}, commit_id_q};

  // If the CPU is ready to execute an instruction, the pipeline will not stall if:
  // 1.The buffer is ready to commit a new instruction, and
  // 2.The buffer has committed all the instructions.
  assign stall_external_o = ~(commit_ready & all_committed);

  assign mem_commit_o = $unsigned($unsigned(commit_id_q) - $unsigned(issue_id_q)) >
                        $unsigned($unsigned(mem_id_low)  - $unsigned(issue_id_q))

  always_comb begin
    // the buffer
    valid_d     = valid_q;
    writeback_d = writeback_q;
    loadstore_d = loadstore_q;
    ecswrite_d  = ecswrite_q;
    exc_d       = exc_q;
    // issue pointer and commit pointer
    issue_id_d  = issue_id_q;
    commit_id_d = commit_id_q;
    if (exc_rst_i) begin
      issue_id_d  = commit_id_q - 1;
      commit_id_d = commit_id_q - 1;
      for (int i = commit_id_q - 1; i < issue_id_q; i++) begin
        valid_d = 1'b0;
      end
    end else begin
      if (issue_accept_i) begin
        // issued instruction with a new id
        issue_id_d = issue_id_q + 1;
        // record the information of the instruction
        valid_d[issue_id_q]     = 1'b1;
        writeback_d[issue_id_q] = issue_wb_i;
        loadstore_d[issue_id_q] = issue_ls_i;
        ecswrite_d[issue_id_q]  = issue_ecsw_i;
        exc_d[issue_id_q]       = issue_exc_i;
      end
      if (mem_result_fin_i) begin
        loadstore_d[mem_result_id_low] = 1'b0;
      end
      if (result_fin_i) begin
        loadstore_d[result_id_low] = 1'b0;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_q     <= '0;
      writeback_q <= '0;
      loadstore_q <= '0;
      ecswrite_q  <= '0;
      exc_q       <= '0;
      issue_id_q  <= '0;
      commit_id_q <= '0;
    end else begin
      valid_q     <= valid_d;
      writeback_q <= writeback_d;
      loadstore_q <= loadstore_d;
      ecswrite_q  <= ecswrite_d;
      exc_q       <= exc_d;
      issue_id_q  <= issue_id_d;
      commit_id_q <= commit_id_d;
    end
  end


endmodule