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

module ibex_xif_issue_commit_buffer import ibex_pkg::*; (
  input  logic                  clk_i,
  input  logic                  rst_ni,

  input  logic                  xif_exception_i,
  input  logic                  wb_exception_i,
  input  logic                  mem_in_wb_i,
  output logic                  external_exc_o,
  output logic                  mem_xif_o,
  output logic                  illegal_insn_o,

  // issue interface
  output logic [X_ID_WIDTH-1:0] issue_id_o,
  output logic                  issue_icb_valid_o,
  // If 1, the issue ID from issue commit buffer is valid.
  input  logic                  issue_valid_i, // X-Interface handshake signal
  input  logic                  issue_handshake_i,
  input  logic                  issue_reject_i,
  input  logic                  issue_exc_i,
  input  logic                  issue_ls_i,

  // commit interface
  output logic                  commit_valid_o,
  output logic [X_ID_WIDTH-1:0] commit_id_o,
  output logic                  commit_kill_o,

  // memory interface
  input  logic [X_ID_WIDTH-1:0] mem_id_i,
  output logic                  mem_commit_o,

  // memory result interface
  input  logic                  mem_result_fin_i, // Mem requests from a certain ID has finished.
  input  logic [X_ID_WIDTH-1:0] mem_result_id_i,

  // result interface
  input  logic                  result_handshake_i,
  input  logic [X_ID_WIDTH-1:0] result_id_i
);

  // issue-commit buffer
  logic [ICB_DEPTH-1:0] icb_valid_d, icb_valid_q;
  logic [ICB_DEPTH-1:0] icb_commit_d, icb_commit_q;
  logic [ICB_DEPTH-1:0] icb_exc_d, icb_exc_q;
  logic [ICB_DEPTH-1:0] icb_mem_d, icb_mem_q;
  logic [ICB_DEPTH-1:0] icb_reject_d, icb_reject_q;

  // IDs
  logic [ICB_DEPTH-1:0]               issue_id_onehot;
  logic [ICB_DEPTH-1:0][ICB_ID_W-1:0] issue_id_or;
  logic [ICB_ID_W-1:0]                issue_id_d, issue_id_q;
  logic                               issue_id_valid_d, issue_id_valid_q;
  logic                               issue_id_new_d, issue_id_new_q;
  logic                               issue_id_wen;
  logic [ICB_ID_W-1:0]                issue_id;
  logic [ICB_ID_W-1:0]                commit_id;
  logic [ICB_ID_W-1:0]                result_id;
  logic [ICB_ID_W-1:0]                mem_id;
  logic [ICB_ID_W-1:0]                mem_result_id;
  logic [X_ID_WIDTH-ICB_ID_W-1:0]     unused_result_id;
  logic [X_ID_WIDTH-ICB_ID_W-1:0]     unused_mem_id;
  logic [X_ID_WIDTH-ICB_ID_W-1:0]     unused_mem_result_id;

  // Control signals
  logic insn_reject;
  logic is_killing;

  // ID FIFO
  logic [ICB_ID_W-1:0] icf_push_data;
  logic                icf_push_valid;
  logic                icf_push_ready;
  logic                icf_push;
  logic [ICB_ID_W-1:0] icf_pop_data;
  logic                icf_pop_valid;
  logic                icf_pop_ready;

  // Last-committed buffer
  logic [ICB_ID_W-1:0] lcb_id_q, lcb_id_d;
  logic                lcb_valid_q, lcb_valid_d;
  logic                lcb_push;
  logic                lcb_pop;

  // State machine
  typedef enum logic { ICB_COMMIT, ICB_KILL } icb_fsm_e;
  icb_fsm_e icb_fsm_q, icb_fsm_d;

  ///////////////////////
  // ID width transfer //
  ///////////////////////

  assign issue_id_o    = {{X_ID_WIDTH-ICB_ID_W{1'b0}}, issue_id};
  assign commit_id_o   = {{X_ID_WIDTH-ICB_ID_W{1'b0}}, commit_id};
  assign result_id     = result_id_i[ICB_ID_W-1:0];
  assign mem_id        = mem_id_i[ICB_ID_W-1:0];
  assign mem_result_id = mem_result_id_i[ICB_ID_W-1:0];

  assign unused_result_id     = result_id_i[X_ID_WIDTH-1:ICB_ID_W];
  assign unused_mem_id        = mem_id_i[X_ID_WIDTH-1:ICB_ID_W];
  assign unused_mem_result_id = mem_result_id_i[X_ID_WIDTH-1:ICB_ID_W];

  ///////////////
  // ID lookup //
  ///////////////

  assign issue_id_onehot[0] = ~icb_valid_d[0];
  for (genvar i = 1; i < ICB_DEPTH; i++) begin : gen_issue_id_onehot
    assign issue_id_onehot[i] = ~icb_valid_d[i] & &icb_valid_d[i-1:0];
  end
  for (genvar i = 0; i < ICB_DEPTH; i++) begin : gen_issue_id_or
    assign issue_id_or[i] = issue_id_onehot[i] ? i : '0;
  end
  // Transfer one-hot signal to id
  always_comb begin
    issue_id_d = '0;
    for (int i = 0; i < ICB_DEPTH; i++) begin
      issue_id_d |= issue_id_or[i];
    end
  end

  assign issue_id = issue_id_q;

  //////////////////////////////
  // commit interface outputs //
  //////////////////////////////

  assign commit_valid_o = icf_pop_ready & icf_pop_valid;
  assign commit_id      = icf_pop_data;
  assign commit_kill_o  = is_killing;

  /////////////////////
  // control signals //
  /////////////////////

  // Keep ID stable by register it, update ID when:
  // 1. The issue-commit buffer is not full, and
  // 2. The old id is no longer valid.
  assign issue_id_wen      = ~(&icb_valid_q) & (~issue_id_valid_q | issue_handshake_i);
  // The id is valid next cycle if:
  // 1. An old id is valid this cycle and the handshake has not finished, or
  // 2. A new id is valid next cycle.
  assign issue_id_valid_d  = (issue_id_valid_q & ~issue_handshake_i) | issue_id_wen;
  // There is a new id to be pushed into the FIFO next cycle if:
  // 1. The id is neither in or pushed into FIFO this cycle, or
  // 2. A new id comes.
  assign issue_id_new_d    = (issue_id_new_q & ~icf_push) | issue_id_wen;
  // The buffer is ready to issue a new instruction if:
  // 1. The current issue id is valid, and
  // 2. This id has been pushed into the FIFO or the FIFO is not full, and
  // 3. There is currently no instruction rejected, and
  // 4. Issue-commit buffer is not in the killing mode.
  assign issue_icb_valid_o = issue_id_valid_q & (~issue_id_new_q | icf_push_ready) &
                             ~insn_reject & ~is_killing;
  assign insn_reject       = |icb_reject_q;
  assign external_exc_o    = |icb_exc_d | |icb_mem_d | insn_reject;
  assign mem_xif_o         = |icb_mem_q;
  assign illegal_insn_o    = icb_reject_q[commit_id] | (issue_reject_i & (issue_id == commit_id));
  assign mem_commit_o      = icb_commit_d[mem_id];

  ///////////////////////
  // issue-commit FIFO //
  ///////////////////////

  assign icf_push_data  = issue_id;
  // Push into the FIFO when the handshake is initialized.
  assign icf_push_valid = issue_id_new_q & issue_valid_i;
  assign icf_push       = icf_push_valid & icf_push_ready;
  // Killing mode: pop and kill.
  // Commit mode: pop and commit when:
  // 1. Last-committed buffer is empty or is popping its data, and
  // 2. There is not any pending mem instruction in wb stage, and
  assign icf_pop_ready  = ((~lcb_valid_q | lcb_pop) & ~mem_in_wb_i) | is_killing;

  // The FIFO holds the IDs of issued but not yet committed instructions.
  prim_fifo_sync #(
    .Width            (ICB_ID_W),
    .Pass             (1'b1),
    .Depth            (ICF_DEPTH),
    .OutputZeroIfEmpty(1'b1)
  ) ic_fifo_i (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .clr_i     (1'b0),

    .wvalid_i(icf_push_valid),
    .wready_o(icf_push_ready),
    .wdata_i (icf_push_data),

    .rvalid_o(icf_pop_valid),
    .rready_i(icf_pop_ready),
    .rdata_o (icf_pop_data),

    .full_o (),
    .depth_o()
  );

  ///////////////////////////
  // last-committed buffer //
  ///////////////////////////

  assign lcb_id_d    = icf_pop_data;
  assign lcb_valid_d = lcb_push | (lcb_valid_q & ~lcb_pop);
  // Push committed instructions into the buffer.
  assign lcb_push = commit_valid_o & ~is_killing & ~icb_reject_q[commit_id];
  // Pop only if the instruction could not raise exception in the future.
  assign lcb_pop = (~icb_exc_q[lcb_id_q] & (~icb_mem_q[lcb_id_q] | mem_result_fin_i)) | is_killing;

  //////////////////////////
  // finite state machine //
  //////////////////////////

  always_comb begin
    icb_fsm_d  = icb_fsm_q;
    is_killing = 1'b0;
    unique case (icb_fsm_q)
      ICB_COMMIT: begin
        is_killing = 1'b0;
        if (xif_exception_i | wb_exception_i) begin
          // kill all issued and not committed instructions
          if (icf_pop_valid) begin
            icb_fsm_d = ICB_KILL;
          end
        end
      end
      ICB_KILL: begin
        // The signal is conservative to avoid comb path from XIF inputs to outputs.
        is_killing = 1'b1;
        if (~icf_pop_valid) begin
          icb_fsm_d = ICB_COMMIT;
        end
      end
      default: begin
        icb_fsm_d   = ICB_COMMIT;
      end
    endcase
  end

  /////////////////////////
  // issue-commit buffer //
  /////////////////////////

  always_comb begin
    icb_valid_d  = icb_valid_q;
    icb_commit_d = icb_commit_q;
    icb_exc_d    = icb_exc_q;
    icb_mem_d    = icb_mem_q;
    icb_reject_d = icb_reject_q;
    if (icf_push) begin
      icb_valid_d[issue_id]   = 1'b1;
      // Set 1 since instruction not yet acceptted could raise exception in the future.
      icb_exc_d[issue_id]   = 1'b1;
    end
    if (issue_handshake_i) begin
      icb_valid_d[issue_id]  = 1'b1;
      icb_exc_d[issue_id]    = issue_exc_i;
      icb_mem_d[issue_id]    = issue_ls_i;
      icb_reject_d[issue_id] = issue_reject_i;
    end
    // If result arrives at the same cycle, overwrite issue
    if (result_handshake_i) begin
      icb_valid_d[result_id]  = 1'b0;
      icb_commit_d[result_id] = 1'b0;
      icb_exc_d[result_id]    = 1'b0;
      icb_mem_d[result_id]    = 1'b0;
    end
    if (mem_result_fin_i) begin
      icb_mem_d[mem_result_id] = 1'b0;
    end
    if (commit_valid_o) begin
      if (icb_reject_q[commit_id] | is_killing) begin
        // Clear all the bits for a rejected or killed instruction
        icb_valid_d[commit_id]  = 1'b0;
        icb_commit_d[commit_id] = 1'b0;
        icb_exc_d[commit_id]    = 1'b0;
        icb_mem_d[commit_id]    = 1'b0;
        icb_reject_d[commit_id] = 1'b0;
      end else begin
        icb_commit_d[commit_id] = 1'b1;
      end
    end
    if (xif_exception_i) begin
      icb_valid_d[lcb_id_q]  = 1'b0;
      icb_commit_d[lcb_id_q] = 1'b0;
      icb_exc_d[lcb_id_q]    = 1'b0;
      icb_mem_d[lcb_id_q]    = 1'b0;
      icb_reject_d[lcb_id_q] = 1'b0;
    end
  end

  ////////////////
  // flip-flops //
  ////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lcb_id_q <= '0;
    end else if (lcb_push) begin
      lcb_id_q <= lcb_id_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      issue_id_q <= '0;
    end else if (issue_id_wen) begin
      issue_id_q <= issue_id_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      issue_id_valid_q <= 1'b0;
      issue_id_new_q   <= 1'b0;
      lcb_valid_q      <= 1'b0;
      icb_fsm_q        <= ICB_COMMIT;
      icb_valid_q      <= '0;
      icb_commit_q     <= '0;
      icb_exc_q        <= '0;
      icb_mem_q        <= '0;
      icb_reject_q     <= '0;
    end else begin
      issue_id_valid_q <= issue_id_valid_d;
      issue_id_new_q   <= issue_id_new_d;
      lcb_valid_q      <= lcb_valid_d;
      icb_fsm_q        <= icb_fsm_d;
      icb_valid_q      <= icb_valid_d;
      icb_commit_q     <= icb_commit_d;
      icb_exc_q        <= icb_exc_d;
      icb_mem_q        <= icb_mem_d;
      icb_reject_q     <= icb_reject_d;
    end
  end

  // Issue interface handshake only if FIFO is not full.
  `ASSERT(IbexICFPushReadyIfValid, icf_push_valid |-> icf_push_ready)

endmodule
