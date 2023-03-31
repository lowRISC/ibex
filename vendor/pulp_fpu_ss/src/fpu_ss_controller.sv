// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// FPU Subsystem Controller
// Contributor: Moritz Imfeld <moimfeld@student.ethz.ch>

module fpu_ss_controller
    import fpu_ss_pkg::*;
#(
    parameter PULP_ZFINX = 0,
    parameter INPUT_BUFFER_DEPTH = 0,
    parameter OUT_OF_ORDER = 1,
    parameter FORWARDING = 1
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    // Predecoder
    input  logic       in_buf_push_ready_i,
    input  logic [2:0] prd_rsp_use_rs_i,

    // Issue Interface
    input  logic [2:0] x_issue_req_rs_valid_i,
    output logic       x_issue_ready_o,

    // Commit Interface
    input  logic       x_commit_valid_i,
    input  x_commit_t  x_commit_i,

    // Input Buffer
    input  logic in_buf_pop_valid_i,
    output logic in_buf_pop_ready_o,

    // Register
    input  logic       rd_is_fp_i,
    input  logic [4:0] fpr_wb_addr_i,
    input  logic [4:0] rd_i,
    output logic       fpr_we_o,
    input  logic [3:0] fpu_out_id_i,

    // Dependency Check and Forwarding
    input  logic                         rd_in_is_fp_i,
    input  logic                   [4:0] rs1_i,
    input  logic                   [4:0] rs2_i,
    input  logic                   [4:0] rs3_i,
    output logic                   [2:0] fpu_fwd_o,
    output logic                   [2:0] lsu_fwd_o,
    input  fpu_ss_pkg::op_select_e [2:0] op_select_i,
    output logic                         dep_rs_o,
    output logic                         dep_rd_o,
    input  logic                         x_issue_ready_i,

    // Memory Instruction
    input logic is_load_i,
    input logic is_store_i,

    // Memory Request/Repsonse Interface
    output logic x_mem_valid_o,
    input  logic x_mem_ready_i,
    output logic x_mem_req_we_o,
    output logic x_mem_req_spec_o,
    output logic x_mem_req_last_o,

    // Memory Buffer
    output logic                      mem_push_valid_o,
    input  logic                      mem_push_ready_i,
    output logic                      mem_pop_ready_o,
    input  fpu_ss_pkg::mem_metadata_t mem_pop_data_i,

    // Memory Result Interface
    input  logic x_mem_result_valid_i,

    // FPnew
    input  logic       use_fpu_i,
    output logic       fpu_in_valid_o,
    input  logic       fpu_in_ready_i,
    input  logic [3:0] fpu_in_id_i,
    input  logic       fpu_out_valid_i,
    output logic       fpu_out_ready_o,

    // Result Interface
    input  logic x_result_ready_i,
    output logic x_result_valid_o,
    input  logic csr_instr_i,
    input  logic csr_instr_rec_i
);

  // dependencies and forwarding
  logic [2:0] valid_operands;
  logic       dep_rs1;
  logic       dep_rs2;
  logic       dep_rs1_add; // seperate dependency for the addition and subtraction instruction, since they have different operand assignments (--> see FPnew documentation)
  logic       dep_rs2_add; // seperate dependency for the addition and subtraction instruction, since they have different operand assignments (--> see FPnew documentation)
  logic       dep_rs3;

  // handshakes
  logic x_result_hs;
  logic x_mem_req_hs;

  // status signals and scoreboards
  logic        instr_inflight_d;
  logic        instr_inflight_q;
  logic        instr_offloaded_d;
  logic        instr_offloaded_q;
  logic [31:0] rd_scoreboard_d;
  logic [31:0] rd_scoreboard_q;
  logic [15:0] id_scoreboard_d;
  logic [15:0] id_scoreboard_q;

  // ---------------
  // Issue Interface
  // ---------------
  always_comb begin
    x_issue_ready_o = 1'b0;
    if (((prd_rsp_use_rs_i[0] & x_issue_req_rs_valid_i[0]) | !prd_rsp_use_rs_i[0])
      & ((prd_rsp_use_rs_i[1] & x_issue_req_rs_valid_i[1]) | !prd_rsp_use_rs_i[1])
      & ((prd_rsp_use_rs_i[2] & x_issue_req_rs_valid_i[2]) | !prd_rsp_use_rs_i[2])
      & in_buf_push_ready_i) begin
      x_issue_ready_o = 1'b1;
    end
  end

  // ------------
  // Input Buffer
  // ------------
  always_comb begin
    in_buf_pop_ready_o = 1'b0;
    if ((fpu_in_valid_o & fpu_in_ready_i) | csr_instr_rec_i | x_mem_req_hs) begin
      in_buf_pop_ready_o = 1'b1;
    end
  end

  // ----------------
  // FP Register File
  // ----------------
  always_comb begin
    fpr_we_o = 1'b0;
    if ((fpu_out_valid_i & fpu_out_ready_o & rd_is_fp_i) | (mem_pop_data_i.we & x_mem_result_valid_i) & ~PULP_ZFINX) begin
      fpr_we_o = 1'b1;
    end
  end

  // -------------------------------
  // Dependency Check and Forwarding
  // -------------------------------
  assign dep_rs1     = rd_scoreboard_q[rs1_i] & in_buf_pop_valid_i & (op_select_i[0] == fpu_ss_pkg::RegA);
  assign dep_rs1_add = rd_scoreboard_q[rs2_i] & in_buf_pop_valid_i & (op_select_i[1] == fpu_ss_pkg::RegA);
  assign dep_rs2     = rd_scoreboard_q[rs2_i] & in_buf_pop_valid_i & (op_select_i[1] == fpu_ss_pkg::RegB);
  assign dep_rs2_add = rd_scoreboard_q[rs3_i] & in_buf_pop_valid_i & (op_select_i[2] == fpu_ss_pkg::RegB);
  assign dep_rs3     = rd_scoreboard_q[rs3_i] & in_buf_pop_valid_i & (op_select_i[2] == fpu_ss_pkg::RegC);
  assign dep_rs_o    = (dep_rs1     & ~(fpu_fwd_o[0] | lsu_fwd_o[0]))
                     | (dep_rs1_add & ~(fpu_fwd_o[1] | lsu_fwd_o[1]))
                     | (dep_rs2     & ~(fpu_fwd_o[1] | lsu_fwd_o[1]))
                     | (dep_rs2_add & ~(fpu_fwd_o[2] | lsu_fwd_o[2]))
                     | (dep_rs3     & ~(fpu_fwd_o[2] | lsu_fwd_o[2]));
  assign dep_rd_o    = rd_scoreboard_q[rd_i] & rd_in_is_fp_i & ~(((fpu_out_valid_i & fpu_out_ready_o) | x_mem_result_valid_i)
                     & fpr_we_o & (fpr_wb_addr_i == rd_i));

  always_comb begin
    fpu_fwd_o[0] = 1'b0;
    fpu_fwd_o[1] = 1'b0;
    fpu_fwd_o[2] = 1'b0;
    lsu_fwd_o[0] = 1'b0;
    lsu_fwd_o[1] = 1'b0;
    lsu_fwd_o[2] = 1'b0;
    if (FORWARDING) begin
      valid_operands[0] = op_select_i[0] == fpu_ss_pkg::RegA;
      valid_operands[1] = op_select_i[1] == fpu_ss_pkg::RegA | op_select_i[1] == fpu_ss_pkg::RegB;
      valid_operands[2] = op_select_i[2] == fpu_ss_pkg::RegB | op_select_i[2] == fpu_ss_pkg::RegC;
      fpu_fwd_o[0] = valid_operands[0] & fpu_out_valid_i & fpu_out_ready_o & rd_is_fp_i & rs1_i == fpr_wb_addr_i;
      fpu_fwd_o[1] = valid_operands[1] & fpu_out_valid_i & fpu_out_ready_o & rd_is_fp_i & rs2_i == fpr_wb_addr_i;
      fpu_fwd_o[2] = valid_operands[2] & fpu_out_valid_i & fpu_out_ready_o & rd_is_fp_i & rs3_i == fpr_wb_addr_i;
      lsu_fwd_o[0] = valid_operands[0] & x_mem_result_valid_i & mem_pop_data_i.we & rs1_i == mem_pop_data_i.rd;
      lsu_fwd_o[1] = valid_operands[1] & x_mem_result_valid_i & mem_pop_data_i.we & rs2_i == mem_pop_data_i.rd;
      lsu_fwd_o[2] = valid_operands[2] & x_mem_result_valid_i & mem_pop_data_i.we & rs3_i == mem_pop_data_i.rd;
    end
  end

  // ----------------------------------
  // Memory Interface and Memory Buffer
  // ----------------------------------
  assign x_mem_req_hs = x_mem_valid_o & x_mem_ready_i;
  assign x_mem_req_spec_o = 1'b1;  // no speculative memory operations -> hardwire to 0

  assign mem_push_valid_o = x_mem_req_hs;
  assign mem_pop_ready_o = x_mem_result_valid_i;

  always_comb begin
    x_mem_valid_o = 1'b0;
    if ((is_load_i | is_store_i) & ~dep_rs_o & ~dep_rd_o & in_buf_pop_valid_i & mem_push_ready_i
       & (x_issue_ready_i || (INPUT_BUFFER_DEPTH != 0))) begin
      x_mem_valid_o = 1'b1;
    end
  end

  always_comb begin
    x_mem_req_we_o = 1'b0;
    if (is_store_i) begin
      x_mem_req_we_o = 1'b1;
    end
  end

  always_comb begin
    x_mem_req_last_o = 1'b0;
    if (x_mem_valid_o) begin
      x_mem_req_last_o = 1'b1;
    end
  end

  // -----
  // FPnew
  // -----
  assign fpu_out_ready_o = ~x_mem_result_valid_i;
  always_comb begin
    fpu_in_valid_o = 1'b0;
    if (use_fpu_i & in_buf_pop_valid_i & (id_scoreboard_q[fpu_in_id_i] | ((x_commit_i.id == fpu_in_id_i)
       & ~x_commit_i.commit_kill)) & ~dep_rs_o & ~dep_rd_o & (x_issue_ready_i | ~PULP_ZFINX) & OUT_OF_ORDER) begin
      fpu_in_valid_o = 1'b1;
    end else if (use_fpu_i  & in_buf_pop_valid_i & (id_scoreboard_q[fpu_in_id_i] | ((x_commit_i.id == fpu_in_id_i)
                & ~x_commit_i.commit_kill)) & ~dep_rs_o & ~dep_rd_o & (fpu_out_valid_i | ~instr_inflight_q) & ~OUT_OF_ORDER) begin
      fpu_in_valid_o = 1'b1;
    end
  end

  // ----------------
  // Result Interface
  // ----------------
  assign x_result_hs = x_result_ready_i & x_result_valid_o;
  always_comb begin
    x_result_valid_o = 1'b0;
    if (fpu_out_valid_i | csr_instr_i | x_mem_result_valid_i) begin
      x_result_valid_o = 1'b1;
    end
  end


  // -----------------------------
  // Status Signals and Scoreboard
  // -----------------------------
  always_comb begin
    instr_inflight_d = instr_inflight_q;
    if ((fpu_out_valid_i & fpu_out_ready_o) & ~fpu_in_valid_o) begin
      instr_inflight_d = 1'b0;
    end else if (fpu_in_valid_o) begin
      instr_inflight_d = 1'b1;
    end
  end

  always_comb begin
    instr_offloaded_d = instr_offloaded_q;
    if (in_buf_pop_valid_i & x_mem_req_hs) begin
      instr_offloaded_d = 1'b1;
    end else if (x_mem_result_valid_i) begin
      instr_offloaded_d = 1'b0;
    end
  end

  always_comb begin
    rd_scoreboard_d = rd_scoreboard_q;
    if ((fpu_in_valid_o & fpu_in_ready_i & rd_in_is_fp_i) | (x_mem_req_hs & is_load_i & in_buf_pop_valid_i)) begin
      rd_scoreboard_d[rd_i] = 1'b1;
    end
    if ((fpu_out_ready_o & fpu_out_valid_i) & ~(fpu_in_valid_o & fpu_in_ready_i & fpr_wb_addr_i == rd_i)) begin
      rd_scoreboard_d[fpr_wb_addr_i] = 1'b0;
    end else if (x_mem_result_valid_i & mem_pop_data_i.we & ~(fpu_in_valid_o & fpu_in_ready_i & rd_in_is_fp_i
                & (mem_pop_data_i.rd == rd_i))) begin
      rd_scoreboard_d[mem_pop_data_i.rd] = 1'b0;
    end
  end

  always_comb begin
    id_scoreboard_d = id_scoreboard_q;
    if (x_commit_valid_i & ~x_commit_i.commit_kill) begin
      id_scoreboard_d[x_commit_i.id] = 1'b1;
    end
    if (fpu_out_ready_o & fpu_out_valid_i) begin
      id_scoreboard_d[fpu_out_id_i] = 1'b0;
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      instr_inflight_q  <= 1'b0;
      instr_offloaded_q <= 1'b0;
      rd_scoreboard_q   <= '0;
      id_scoreboard_q   <= '0;
    end else begin
      instr_inflight_q  <= instr_inflight_d;
      instr_offloaded_q <= instr_offloaded_d;
      rd_scoreboard_q   <= rd_scoreboard_d;
      id_scoreboard_q   <= id_scoreboard_d;
    end
  end

endmodule // fpu_ss_controller
