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
// Description: Top level Module of the FPU subsystem
//
// Parameters:  PULP_ZFINX:         Enable support for "Zfinx" standard extension (and thereby removing support for
//                                  "F" standard extension)
//
//              INPUT_BUFFER_DEPTH: Set depth of the FIFO input buffer. If parameter is set to 0, no buffer will be
//                                  instantiated
//
//              OUT_OF_ORDER:       Enable out-of-order execution for instructions that go through
//                                  the FPnew.
//                                  For example with OUT_OF_ORDER = 1
//                                      fdiv.s fa1, fa2, fa3 // suppose takes 3 cycles
//                                      fmul.s fa4, fa5, fa6 // suppose takes 1 cycles
//                                      fmul.s fa2, fa5, fa6 // suppose takes 1 cycles
//                                      fmul.s fa3, fa5, fa6 // suppose takes 1 cycles
//                                  --> This sequence takes 4 clock cycles
//                                  With OUT_OF_ORDER this instruction sequence would take 5 clock cycles
//                                  Possible values for this parameter are 0 and 1
//
//             FORWARDING:          Enable forwarding of floating-point results in the subsystem.
//                                  For examle take this sequence:
//                                      fmul.s fa4, fa5, fa6 // suppose takes 1 cycles
//                                      fmul.s fa1, fa4, fa6 // suppose takes 1 cycles
//                                  There is a source register dependency for the second instruction on the
//                                  first instructions result. With FORWARDING = 1 this sequence takes 2 clock cycles
//                                  while with FORWARDING = 0 this sequence takes 3 clock cycles.
//
//             FPU_FEATURES:        Parameter to configure the FPnew. The subsystem was designed for the configuration found here:
//                                  https://github.com/moimfeld/cv32e40p/blob/x-interface/example_tb/core/fpu_ss/fpu_ss_pkg.sv
//                                  Other configurations might not work
//
//             FPU_IMPLEMENTATION:  Parameter to configure the FPnew. The subsystem was designed for the configuration found here:
//                                  https://github.com/moimfeld/cv32e40p/blob/x-interface/example_tb/core/fpu_ss/fpu_ss_pkg.sv
//                                  Other configurations might not work
//
// Contributor: Moritz Imfeld <moimfeld@student.ethz.ch>
//              Davide Schiavone <davide@openhwgroup.org>

module fpu_ss
    import fpu_ss_pkg::*;
#(
    parameter                                 PULP_ZFINX         = 0,
    parameter                                 INPUT_BUFFER_DEPTH = 0,
    parameter                                 OUT_OF_ORDER       = 1,
    parameter                                 FORWARDING         = 1,
    parameter fpnew_pkg::fpu_features_t       FPU_FEATURES       = fpu_ss_pkg::FPU_FEATURES,
    parameter fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = fpu_ss_pkg::FPU_IMPLEMENTATION
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    // Compressed Interface
    input  logic x_compressed_valid_i,
    output logic x_compressed_ready_o,
    input  x_compressed_req_t x_compressed_req_i,
    output x_compressed_resp_t x_compressed_resp_o,

    // Issue Interface
    input  logic x_issue_valid_i,
    output logic x_issue_ready_o,
    input  x_issue_req_t x_issue_req_i,
    output x_issue_resp_t x_issue_resp_o,

    // Commit Interface
    input  logic x_commit_valid_i,
    input  x_commit_t x_commit_i,

    // Memory Eequest/Response Interface
    output logic x_mem_valid_o,
    input  logic x_mem_ready_i,
    output x_mem_req_t x_mem_req_o,
    input  x_mem_resp_t x_mem_resp_i,

    // Memory Result Interface
    input  logic x_mem_result_valid_i,
    input  x_mem_result_t x_mem_result_i,

    // Result Interface
    output logic x_result_valid_o,
    input  logic x_result_ready_i,
    output x_result_t x_result_o
);

// predecoder parameter
`ifdef PULP_ZFINX_DEF
  localparam int unsigned NUM_INSTR                   = fpu_ss_prd_zfinx_pkg::NumInstr;
  localparam offload_instr_t OFFLOAD_INSTR[NUM_INSTR] = fpu_ss_prd_zfinx_pkg::OffloadInstr;
`else
  localparam int unsigned NUM_INSTR                   = fpu_ss_prd_f_pkg::NumInstr;
  localparam offload_instr_t OFFLOAD_INSTR[NUM_INSTR] = fpu_ss_prd_f_pkg::OffloadInstr;
`endif

  // compressed predecoder signals
  comp_prd_req_t                                  comp_prd_req;
  comp_prd_rsp_t                                  comp_prd_rsp;

  // predecoder signals
  acc_prd_req_t                                   prd_req;
  acc_prd_rsp_t                                   prd_rsp;
  logic                                           in_buf_push_ready;

  // issue_interface
  logic                                           x_issue_ready;

  // input stream fifo signals
  offloaded_data_t                                in_buf_push_data;
  offloaded_data_t                                in_buf_pop_data;
  logic                                           in_buf_push_valid;
  logic                                           in_buf_pop_valid;
  logic                                           in_buf_pop_ready;

  // decoder signals
  fpnew_pkg::operation_e                          fpu_op;
  op_select_e                  [       2:0      ] op_select_dec;
  op_select_e                  [       2:0      ] op_select;
  fpnew_pkg::roundmode_e                          fpu_rnd_mode;
  logic                                           set_dyn_rm;
  fpnew_pkg::fp_format_e                          src_fmt;
  fpnew_pkg::fp_format_e                          dst_fmt;
  fpnew_pkg::int_format_e                         int_fmt;
  logic                                           rd_is_fp;
  logic                                           csr_instr;
  logic                                           csr_instr_rec;
  logic                                           vectorial_op;
  logic                                           op_mode;
  logic                                           use_fpu;
  logic                                           is_store;
  logic                                           is_load;
  ls_size_e                                       ls_size;
  logic                                           error;

  // forwarding and dependency
  logic                          [ 2:0]           fpu_fwd;
  logic                          [ 2:0]           lsu_fwd;
  logic                                           dep_rs;
  logic                                           dep_rd;

  // instruction data, operands and adresses
  logic                          [31:0]           instr;
  logic                          [ 2:0]   [31:0]  fpu_operands_dec;
  logic                          [ 2:0]   [31:0]  fpu_operands;
  logic                          [ 2:0]   [31:0]  int_operands;
  logic                          [ 2:0]   [31:0]  fpr_operands;
  logic                          [ 4:0]           rs1;
  logic                          [ 4:0]           rs2;
  logic                          [ 4:0]           rs3;
  logic                          [ 4:0]           rd;
  logic                          [31:0]           offset;
  logic                          [ 2:0]   [ 4:0]  fpr_raddr;
  logic                          [ 4:0]           fpr_wb_addr;
  logic                          [31:0]           fpr_wb_data;
  logic                                           fpr_we;

  // memory buffer signals
  logic                                           mem_push_valid;
  logic                                           mem_push_ready;
  logic                                           mem_pop_valid;
  logic                                           mem_pop_ready;
  mem_metadata_t                                  mem_push_data;
  mem_metadata_t                                  mem_pop_data;

  // CSR
  logic                                           csr_wb;
  logic                          [31:0]           csr_rdata;
  logic                          [ 4:0]           csr_wb_addr;
  logic                          [ 3:0]           csr_wb_id;
  logic                          [ 2:0]           frm;

  // FPnew signals
  fpu_tag_t                                       fpu_tag_in;
  fpu_tag_t                                       fpu_tag_out;
  logic                                           fpu_in_valid;
  logic                                           fpu_in_ready;
  logic                                           fpu_out_valid;
  logic                                           fpu_out_ready;
  logic                          [31:0]           fpu_result;
  logic                                           fpu_busy;
  fpnew_pkg::status_t                             fpu_status;

  // compressed interface signal assignments
  assign x_compressed_ready_o = x_compressed_valid_i;
  assign comp_prd_req.comp_instr = x_compressed_req_i.instr;
  assign x_compressed_resp_o.instr = comp_prd_rsp.decomp_instr;
  assign x_compressed_resp_o.accept = comp_prd_rsp.accept;

  // issue interface signal assignment
  assign prd_req.q_instr_data = x_issue_req_i.instr;
  assign x_issue_resp_o.accept = prd_rsp.p_accept;
  assign x_issue_resp_o.writeback = prd_rsp.p_writeback;
  assign x_issue_resp_o.loadstore = prd_rsp.p_is_mem_op;
  assign x_issue_resp_o.dualwrite = '0;
  assign x_issue_resp_o.dualread  = '0;
  assign x_issue_resp_o.ecswrite  = '0;
  assign x_issue_resp_o.exc = '0;

  // input buffer signal assignment
  assign in_buf_push_valid = x_issue_valid_i & x_issue_ready_o;
  assign in_buf_push_data.rs = x_issue_req_i.rs;
  assign in_buf_push_data.instr_data = x_issue_req_i.instr;
  assign in_buf_push_data.id = x_issue_req_i.id;
  assign in_buf_push_data.mode = x_issue_req_i.mode;

  // instr, operand and address signal assignment
  assign instr = in_buf_pop_data.instr_data;
  assign int_operands[0] = in_buf_pop_data.rs[0];
  assign int_operands[1] = in_buf_pop_data.rs[1];
  assign int_operands[2] = in_buf_pop_data.rs[2];
  assign rs1 = instr[19:15];
  assign rs2 = instr[24:20];
  assign rs3 = instr[31:27];
  assign rd  = instr[11:7];

  // FPnew tag
  assign fpu_tag_in.addr = rd;
  assign fpu_tag_in.rd_is_fp = rd_is_fp;
  assign fpu_tag_in.id = in_buf_pop_data.id;

  // memory instruction buffer assignment
  assign mem_push_data.id   = in_buf_pop_data.id;
  assign mem_push_data.rd   = rd;
  assign mem_push_data.we   = is_load;

  // memory request signal assignments
  assign x_mem_req_o.mode   = in_buf_pop_data.mode;
  assign x_mem_req_o.size   = {1'b0, instr[14:12]};
  assign x_mem_req_o.id     = in_buf_pop_data.id;
  assign x_mem_req_o.attr   = 2'b00;
  assign x_mem_req_o.be     = 4'b1111;

  always_comb begin
    x_mem_req_o.wdata = fpr_operands[1];
    if (fpu_fwd[1]) begin
      x_mem_req_o.wdata = fpu_result;
    end else if (lsu_fwd[1]) begin
      x_mem_req_o.wdata = x_mem_result_i.rdata;
    end
  end

  // load and store address calculation for memory instructions
  always_comb begin
    if (~x_mem_req_o.we) begin
      offset = instr[31:20];
      if (instr[31]) begin
        offset = {20'b1111_1111_1111_1111_1111, instr[31:20]};
      end
    end else begin
      offset = {instr[31:25], instr[11:7]};
      if (instr[31]) begin
        offset = {20'b1111_1111_1111_1111_1111, instr[31:25], instr[11:7]};
      end
    end
    x_mem_req_o.addr = int_operands[0] + offset;
  end

  // ---------------------
  // Compressed Predecoder
  // ---------------------
  fpu_ss_compressed_predecoder fpu_ss_compressed_predecoder_i
    (
      .prd_req_i(comp_prd_req),
      .prd_rsp_o(comp_prd_rsp)
  );

  // ----------
  // Predecoder
  // ----------
  fpu_ss_predecoder #(
      .NumInstr(NUM_INSTR),
      .OffloadInstr(OFFLOAD_INSTR)
  ) fpu_ss_predecoder_i (
      .prd_req_i(prd_req),
      .prd_rsp_o(prd_rsp)
  );

  // -----------------
  // Input Stream FIFO
  // -----------------
  generate
    if (INPUT_BUFFER_DEPTH > 0) begin : gen_input_stream_fifo
      stream_fifo #(
          .FALL_THROUGH(1),
          .DATA_WIDTH  (32),
          .DEPTH       (INPUT_BUFFER_DEPTH),
          .T           (offloaded_data_t)
      ) input_stream_fifo_i (
          .clk_i     (clk_i),
          .rst_ni    (rst_ni),
          .flush_i   (1'b0),
          .testmode_i(1'b0),
          .usage_o   (  /* unused */),

          .data_i (in_buf_push_data),
          .valid_i(in_buf_push_valid),
          .ready_o(in_buf_push_ready),

          .data_o (in_buf_pop_data),
          .valid_o(in_buf_pop_valid),
          .ready_i(in_buf_pop_ready)
      );
      assign x_issue_ready_o = x_issue_ready;
    end else begin : gen_no_input_stream_fifo
      assign in_buf_pop_data = in_buf_push_data;
      assign x_issue_ready_o = x_issue_ready & ~dep_rs & ~dep_rd; // readiness of FPnew is assumed here
      assign in_buf_push_ready = 1'b1;
      assign in_buf_pop_valid = x_issue_valid_i;
    end
  endgenerate

  // -------
  // Decoder
  // -------
  fpu_ss_decoder #(
      .PULP_ZFINX(PULP_ZFINX)
  ) fpu_ss_decoder_i (
      .instr_i       (instr),
      .fpu_rnd_mode_i(fpnew_pkg::roundmode_e'(frm)),
      .fpu_op_o      (fpu_op),
      .op_select_o   (op_select_dec),
      .fpu_rnd_mode_o(fpu_rnd_mode),
      .set_dyn_rm_o  (set_dyn_rm),
      .src_fmt_o     (src_fmt),
      .dst_fmt_o     (dst_fmt),
      .int_fmt_o     (int_fmt),
      .rd_is_fp_o    (rd_is_fp),
      .vectorial_op_o(vectorial_op),
      .op_mode_o     (op_mode),
      .use_fpu_o     (use_fpu),
      .is_store_o    (is_store),
      .is_load_o     (is_load),
      .ls_size_o     (ls_size)
  );

  // ------------------------------
  // Memory Instruction Stream FIFO
  // ------------------------------
  stream_fifo #(
      .FALL_THROUGH(0),
      .DATA_WIDTH  (32),
      .DEPTH       (3),
      .T           (mem_metadata_t)
  ) mem_stream_fifo_i (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .flush_i   (1'b0),
      .testmode_i(1'b0),
      .usage_o   (  /* unused */),

      .data_i (mem_push_data),
      .valid_i(mem_push_valid),
      .ready_o(mem_push_ready),

      .data_o (mem_pop_data),
      .valid_o(mem_pop_valid),
      .ready_i(mem_pop_ready)
  );

  // ------------------
  // Floating-Point CSR
  // ------------------
  fpu_ss_csr fpu_ss_csr_i (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .instr_i            (instr),
      .csr_data_i         (int_operands[0]),
      .fpu_status_i       (fpu_status),
      .in_buf_pop_valid_i (in_buf_pop_valid),
      .fpu_out_valid_i    (fpu_out_valid),
      .csr_id_i           (in_buf_pop_data.id),
      .csr_rdata_o        (csr_rdata),
      .frm_o              (frm),
      .csr_wb_o           (csr_wb),
      .csr_wb_addr_o      (csr_wb_addr),
      .csr_wb_id_o        (csr_wb_id),
      .csr_instr_o        (csr_instr),
      .csr_instr_rec_o    (csr_instr_rec)
  );

  // ------------------------
  // FPU Subsystem Controller
  // ------------------------
  fpu_ss_controller #(
      .PULP_ZFINX(PULP_ZFINX),
      .INPUT_BUFFER_DEPTH(INPUT_BUFFER_DEPTH),
      .OUT_OF_ORDER(OUT_OF_ORDER),
      .FORWARDING(FORWARDING)
  ) fpu_ss_controller_i (
      // Clock and Reset
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      // Predecoder
      .in_buf_push_ready_i (in_buf_push_ready),
      .prd_rsp_use_rs_i (prd_rsp.p_use_rs),

      // Issue Interface
      .x_issue_req_rs_valid_i (x_issue_req_i.rs_valid),
      .x_issue_ready_o  (x_issue_ready),

      // Commit Interface
      .x_commit_valid_i (x_commit_valid_i),
      .x_commit_i       (x_commit_i),

      // Input Buffer
      .in_buf_pop_valid_i (in_buf_pop_valid),
      .in_buf_pop_ready_o (in_buf_pop_ready),

      // Register
      .rd_is_fp_i(fpu_tag_out.rd_is_fp),
      .fpr_wb_addr_i(fpr_wb_addr),
      .rd_i(rd),
      .fpr_we_o(fpr_we),
      .fpu_out_id_i (fpu_tag_out.id),

      // Dependency Check and Forwarding
      .rd_in_is_fp_i(rd_is_fp),
      .rs1_i(fpr_raddr[0]),
      .rs2_i(fpr_raddr[1]),
      .rs3_i(fpr_raddr[2]),
      .fpu_fwd_o(fpu_fwd),
      .lsu_fwd_o(lsu_fwd),
      .op_select_i(op_select),
      .dep_rs_o(dep_rs),
      .dep_rd_o(dep_rd),
      .x_issue_ready_i(x_issue_ready_o),

      // Memory Instruction
      .is_load_i (is_load),
      .is_store_i(is_store),

      // Memory Request/Repsonse Interface
      .x_mem_valid_o    (x_mem_valid_o),
      .x_mem_ready_i    (x_mem_ready_i),
      .x_mem_req_we_o   (x_mem_req_o.we),
      .x_mem_req_spec_o (x_mem_req_o.spec),
      .x_mem_req_last_o (x_mem_req_o.last),

      // Memory Buffer
      .mem_push_valid_o (mem_push_valid),
      .mem_push_ready_i (mem_push_ready),
      .mem_pop_ready_o  (mem_pop_ready),
      .mem_pop_data_i   (mem_pop_data),

      // Memory Result Interface
      .x_mem_result_valid_i(x_mem_result_valid_i),

      // FPnew
      .fpu_in_valid_o  (fpu_in_valid),
      .fpu_in_ready_i  (fpu_in_ready),
      .use_fpu_i       (use_fpu),
      .fpu_in_id_i     (in_buf_pop_data.id),
      .fpu_out_valid_i (fpu_out_valid),
      .fpu_out_ready_o (fpu_out_ready),

      // Result Interface
      .x_result_ready_i(x_result_ready_i),
      .x_result_valid_o(x_result_valid_o),
      .csr_instr_i(csr_instr),
      .csr_instr_rec_i(csr_instr_rec)
  );

  // -------------------------------------
  // Floating-Point specific Register File
  // -------------------------------------
  generate
    if (!PULP_ZFINX) begin : gen_fp_register_file
      // fp register address selection
      always_comb begin
        fpr_raddr[0] = rs1;
        fpr_raddr[1] = rs2;
        fpr_raddr[2] = rs3;

        unique case (op_select_dec[1])
          RegA: begin
            fpr_raddr[1] = rs1;
          end
          default: ;
        endcase

        unique case (op_select_dec[2])
          RegB, RegBRep: begin
            fpr_raddr[2] = rs2;
          end
          RegDest: begin
            fpr_raddr[2] = rd;
          end
          default: ;
        endcase
      end

      // fp register writeback data mux
      always_comb begin
        fpr_wb_data = fpu_result;
        if (x_mem_result_valid_i) begin
          fpr_wb_data = x_mem_result_i.rdata;
        end
      end

      // fp register addr writeback mux
      always_comb begin
        fpr_wb_addr = fpu_tag_out.addr;
        if (x_mem_result_valid_i) begin
          fpr_wb_addr = mem_pop_data.rd;
        end else if (~use_fpu & ~fpu_out_valid) begin
          fpr_wb_addr = rd;
        end
      end

      fpu_ss_regfile fpu_ss_regfile_i (
          .clk_i(clk_i),
          .rst_ni(rst_ni),

          .raddr_i(fpr_raddr),
          .rdata_o(fpr_operands),

          .waddr_i(fpr_wb_addr),
          .wdata_i(fpr_wb_data),
          .we_i   (fpr_we)
      );
    end else begin : gen_no_fp_register_file
      assign fpr_operands = int_operands;
    end
  endgenerate

  // ------------------
  //  Operand Selection
  // ------------------
  for (genvar i = 0; i < 3; i++) begin
    always_comb begin
      op_select[i] = op_select_dec[i];
      if (PULP_ZFINX) begin
        unique case (op_select_dec[i])
          None, AccBus: begin
            op_select[i] = op_select_dec[i];
          end
          RegA, RegB, RegBRep, RegC, RegDest: begin
            op_select[i] = AccBus;
          end
        endcase
      end
    end
  end

  for (genvar i = 0; i < 3; i++) begin : gen_operand_select
    always_comb begin
      unique case (op_select[i])
        None: begin
          fpu_operands_dec[i] = '1;
        end
        AccBus: begin
          fpu_operands_dec[i] = int_operands[i];
          if (fpu_fwd[i]) begin
            fpu_operands_dec[i] = fpu_result;
          end
        end
        RegA, RegB, RegBRep, RegC, RegDest: begin
          fpu_operands_dec[i] = fpr_operands[i];
          if (fpu_fwd[i] & (fpu_op != fpnew_pkg::ADD)) begin
            fpu_operands_dec[i] = fpu_result;
          end else if (lsu_fwd[i] & (fpu_op != fpnew_pkg::ADD)) begin
            fpu_operands_dec[i] = x_mem_result_i.rdata;
          end
          // Replicate if needed
          if (op_select[i] == RegBRep) begin
            unique case (src_fmt)
              fpnew_pkg::FP32: fpu_operands_dec[i] = {(32 / 32) {fpu_operands_dec[i][31:0]}};
              fpnew_pkg::FP16, fpnew_pkg::FP16ALT:
              fpu_operands_dec[i] = {(32 / 16) {fpu_operands_dec[i][15:0]}};
              fpnew_pkg::FP8: fpu_operands_dec[i] = {(32 / 8) {fpu_operands_dec[i][7:0]}};
              default: fpu_operands_dec[i] = fpu_operands_dec[i][32-1:0];
            endcase
          end
        end
        default: begin
          fpu_operands_dec[i] = '0;
        end
      endcase
    end
  end

  always_comb begin
    fpu_operands = fpu_operands_dec;
    if (PULP_ZFINX) begin
      if (op_select_dec[1] == RegA) begin
        fpu_operands[1] = int_operands[0];
      end
      if (op_select_dec[2] == RegB) begin
        fpu_operands[2] = int_operands[1];
      end
    end else begin
      if (lsu_fwd[1] & (fpu_op == fpnew_pkg::ADD) & use_fpu) begin
        fpu_operands[1] = x_mem_result_i.rdata;
      end
      if (lsu_fwd[2] & (fpu_op == fpnew_pkg::ADD) & use_fpu) begin
        fpu_operands[2] = x_mem_result_i.rdata;
      end
      if (fpu_fwd[1] & (fpu_op == fpnew_pkg::ADD) & use_fpu) begin
        fpu_operands[1] = fpu_result;
      end
      if (fpu_fwd[2] & (fpu_op == fpnew_pkg::ADD) & use_fpu) begin
        fpu_operands[2] = fpu_result;
      end
    end
  end

  // ------
  //  FPnew
  // ------
  fpnew_top #(
      .Features      (FPU_FEATURES),
      .Implementation(FPU_IMPLEMENTATION),
      .TagType       (fpu_tag_t)
  ) i_fpnew_bulk (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .operands_i    (fpu_operands),
      .rnd_mode_i    (fpnew_pkg::roundmode_e'(fpu_rnd_mode)),
      .op_i          (fpnew_pkg::operation_e'(fpu_op)),
      .op_mod_i      (op_mode),
      .src_fmt_i     (fpnew_pkg::fp_format_e'(src_fmt)),
      .dst_fmt_i     (fpnew_pkg::fp_format_e'(dst_fmt)),
      .int_fmt_i     (fpnew_pkg::int_format_e'(int_fmt)),
      .vectorial_op_i(vectorial_op),
      .tag_i         (fpu_tag_in),
      .in_valid_i    (fpu_in_valid),
      .in_ready_o    (fpu_in_ready),
      .flush_i       (1'b0),
      .result_o      (fpu_result),
      .status_o      (fpu_status),
      .tag_o         (fpu_tag_out),
      .out_valid_o   (fpu_out_valid),
      .out_ready_i   (fpu_out_ready),
      .busy_o        (fpu_busy)
  );

  // -------------------------
  //  Result Interface Signals
  // -------------------------
  assign x_result_o.exc     = 1'b0;  // no errors can occur for now
  assign x_result_o.exccode = '0; // no errors can occur for now
  assign x_result_o.err     = 1'b0;
  assign x_result_o.dbg     = 1'b0;

  always_comb begin
    x_result_o.data = fpu_result;
    if (csr_wb & ~fpu_out_valid & csr_wb & ~fpu_out_valid) begin
      x_result_o.data = csr_wb_addr;
    end
  end

  always_comb begin
    x_result_o.rd = '0;
    x_result_o.id = '0;
    if (x_result_valid_o) begin
      if (fpu_out_valid) begin
        x_result_o.rd = fpu_tag_out.addr;
        x_result_o.id = fpu_tag_out.id;
      end else if (csr_instr) begin
        x_result_o.rd = csr_wb_addr;
        x_result_o.id = csr_wb_id;
      end else begin
        x_result_o.id = mem_pop_data.id;
      end
    end
  end

  always_comb begin
    x_result_o.we = 1'b0;
    if ((fpu_out_valid & ~fpu_tag_out.rd_is_fp) | (csr_wb)) begin
      x_result_o.we = 1'b1;
    end
  end

  always_comb begin
    x_result_o.ecswe   = '0;
    x_result_o.ecsdata = '0;
    if (fpu_out_valid & x_result_valid_o & fpu_tag_out.rd_is_fp) begin
      x_result_o.ecswe   = 3'b010;
      x_result_o.ecsdata = 6'b001100;
    end
  end

endmodule  // fpu_ss
