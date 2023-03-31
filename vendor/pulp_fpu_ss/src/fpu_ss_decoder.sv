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
// FPU Subsystem Decoder
// Contributor: Moritz Imfeld <moimfeld@student.ethz.ch>
// Based on: https://github.com/pulp-platform/snitch/blob/master/hw/ip/snitch_cluster/src/snitch_fp_ss.sv

module fpu_ss_decoder #(
    parameter PULP_ZFINX = 0
) (
    input  logic                   [31:0] instr_i,
    input  fpnew_pkg::roundmode_e         fpu_rnd_mode_i,
    output fpnew_pkg::operation_e         fpu_op_o,
    output fpu_ss_pkg::op_select_e [ 2:0] op_select_o,
    output fpnew_pkg::roundmode_e         fpu_rnd_mode_o,
    output logic                          set_dyn_rm_o,
    output fpnew_pkg::fp_format_e         src_fmt_o,
    output fpnew_pkg::fp_format_e         dst_fmt_o,
    output fpnew_pkg::int_format_e        int_fmt_o,
    output logic                          rd_is_fp_o,
    output logic                          vectorial_op_o,
    output logic                          op_mode_o,
    output logic                          use_fpu_o,
    output logic                          is_store_o,
    output logic                          is_load_o,
    output fpu_ss_pkg::ls_size_e          ls_size_o
);

  logic rd_is_fp_dec;

  assign rd_is_fp_o = PULP_ZFINX ? 1'b0 : rd_is_fp_dec;

  always_comb begin

    fpu_op_o = fpnew_pkg::ADD;
    use_fpu_o = 1'b1;
    fpu_rnd_mode_o = (fpnew_pkg::roundmode_e'(instr_i[14:12]) == fpnew_pkg::DYN)
                   ? fpu_rnd_mode_i
                   : fpnew_pkg::roundmode_e'(instr_i[14:12]);

    set_dyn_rm_o = 1'b0;

    src_fmt_o = fpnew_pkg::FP32;
    dst_fmt_o = fpnew_pkg::FP32;
    int_fmt_o = fpnew_pkg::INT32;

    op_select_o[0] = fpu_ss_pkg::None;
    op_select_o[1] = fpu_ss_pkg::None;
    op_select_o[2] = fpu_ss_pkg::None;

    vectorial_op_o = 1'b0;
    op_mode_o = 1'b0;

    is_store_o = 1'b0;
    is_load_o = 1'b0;
    ls_size_o = fpu_ss_pkg::Word;

    // Destination register is in FPR
    rd_is_fp_dec = 1'b1;

    unique casez (instr_i)
      // FP - FP Operations
      // Single Precision
      fpu_ss_instr_pkg::FADD_S: begin
        fpu_op_o = fpnew_pkg::ADD;
        op_select_o[1] = fpu_ss_pkg::RegA;
        op_select_o[2] = fpu_ss_pkg::RegB;
      end
      fpu_ss_instr_pkg::FSUB_S: begin
        fpu_op_o = fpnew_pkg::ADD;
        op_select_o[1] = fpu_ss_pkg::RegA;
        op_select_o[2] = fpu_ss_pkg::RegB;
        op_mode_o = 1'b1;
      end
      fpu_ss_instr_pkg::FMUL_S: begin
        fpu_op_o = fpnew_pkg::MUL;
        op_select_o[0] = fpu_ss_pkg::RegA;
        op_select_o[1] = fpu_ss_pkg::RegB;
      end
      fpu_ss_instr_pkg::FDIV_S: begin
        fpu_op_o = fpnew_pkg::DIV;
        op_select_o[0] = fpu_ss_pkg::RegA;
        op_select_o[1] = fpu_ss_pkg::RegB;
      end
      fpu_ss_instr_pkg::FSGNJ_S, fpu_ss_instr_pkg::FSGNJN_S, fpu_ss_instr_pkg::FSGNJX_S: begin
        fpu_op_o = fpnew_pkg::SGNJ;
        op_select_o[0] = fpu_ss_pkg::RegA;
        op_select_o[1] = fpu_ss_pkg::RegB;
      end
      fpu_ss_instr_pkg::FMIN_S, fpu_ss_instr_pkg::FMAX_S: begin
        fpu_op_o = fpnew_pkg::MINMAX;
        op_select_o[0] = fpu_ss_pkg::RegA;
        op_select_o[1] = fpu_ss_pkg::RegB;
      end
      fpu_ss_instr_pkg::FSQRT_S: begin
        fpu_op_o = fpnew_pkg::SQRT;
        op_select_o[0] = fpu_ss_pkg::RegA;
      end
      fpu_ss_instr_pkg::FMADD_S: begin
        fpu_op_o = fpnew_pkg::FMADD;
        op_select_o[0] = fpu_ss_pkg::RegA;
        op_select_o[1] = fpu_ss_pkg::RegB;
        op_select_o[2] = fpu_ss_pkg::RegC;
      end
      fpu_ss_instr_pkg::FMSUB_S: begin
        fpu_op_o       = fpnew_pkg::FMADD;
        op_select_o[0] = fpu_ss_pkg::RegA;
        op_select_o[1] = fpu_ss_pkg::RegB;
        op_select_o[2] = fpu_ss_pkg::RegC;
        op_mode_o      = 1'b1;
      end
      fpu_ss_instr_pkg::FNMSUB_S: begin
        fpu_op_o = fpnew_pkg::FNMSUB;
        op_select_o[0] = fpu_ss_pkg::RegA;
        op_select_o[1] = fpu_ss_pkg::RegB;
        op_select_o[2] = fpu_ss_pkg::RegC;
      end
      fpu_ss_instr_pkg::FNMADD_S: begin
        fpu_op_o       = fpnew_pkg::FNMSUB;
        op_select_o[0] = fpu_ss_pkg::RegA;
        op_select_o[1] = fpu_ss_pkg::RegB;
        op_select_o[2] = fpu_ss_pkg::RegC;
        op_mode_o      = 1'b1;
      end
      // -------------------
      // From float to int
      // -------------------
      // Single Precision Floating-Point
      fpu_ss_instr_pkg::FLE_S, fpu_ss_instr_pkg::FLT_S, fpu_ss_instr_pkg::FEQ_S: begin
        fpu_op_o       = fpnew_pkg::CMP;
        op_select_o[0] = fpu_ss_pkg::RegA;
        op_select_o[1] = fpu_ss_pkg::RegB;
        src_fmt_o      = fpnew_pkg::FP32;
        dst_fmt_o      = fpnew_pkg::FP32;
        rd_is_fp_dec     = 1'b0;
      end
      fpu_ss_instr_pkg::FCLASS_S: begin
        fpu_op_o       = fpnew_pkg::CLASSIFY;
        op_select_o[0] = fpu_ss_pkg::RegA;
        fpu_rnd_mode_o = fpnew_pkg::RNE;
        src_fmt_o      = fpnew_pkg::FP32;
        dst_fmt_o      = fpnew_pkg::FP32;
        rd_is_fp_dec     = 1'b0;
      end
      fpu_ss_instr_pkg::FCVT_W_S, fpu_ss_instr_pkg::FCVT_WU_S: begin
        fpu_op_o       = fpnew_pkg::F2I;
        op_select_o[0] = fpu_ss_pkg::RegA;
        src_fmt_o      = fpnew_pkg::FP32;
        dst_fmt_o      = fpnew_pkg::FP32;
        rd_is_fp_dec     = 1'b0;
        if (instr_i inside {fpu_ss_instr_pkg::FCVT_WU_S}) op_mode_o = 1'b1;  // unsigned
      end
      fpu_ss_instr_pkg::FMV_X_W: begin
        fpu_op_o       = fpnew_pkg::SGNJ;
        fpu_rnd_mode_o = fpnew_pkg::RUP;  // passthrough without checking nan-box
        src_fmt_o      = fpnew_pkg::FP32;
        dst_fmt_o      = fpnew_pkg::FP32;
        op_mode_o      = 1'b1;  // sign-extend result
        op_select_o[0] = fpu_ss_pkg::RegA;
        rd_is_fp_dec     = 1'b0;
      end
      // -------------------
      // From int to float
      // -------------------
      // Single Precision Floating-Point
      fpu_ss_instr_pkg::FMV_W_X: begin
        fpu_op_o       = fpnew_pkg::SGNJ;
        op_select_o[0] = fpu_ss_pkg::AccBus;
        fpu_rnd_mode_o = fpnew_pkg::RUP;  // passthrough without checking nan-box
        src_fmt_o      = fpnew_pkg::FP32;
        dst_fmt_o      = fpnew_pkg::FP32;
      end
      fpu_ss_instr_pkg::FCVT_S_W, fpu_ss_instr_pkg::FCVT_S_WU: begin
        fpu_op_o       = fpnew_pkg::I2F;
        op_select_o[0] = fpu_ss_pkg::AccBus;
        dst_fmt_o      = fpnew_pkg::FP32;
        if (instr_i inside {fpu_ss_instr_pkg::FCVT_S_WU}) op_mode_o = 1'b1;  // unsigned
      end
      // -------------
      // Load / Store
      // -------------
      // Single Precision Floating-Point
      fpu_ss_instr_pkg::FLW: begin
        is_load_o = 1'b1;
        use_fpu_o = 1'b0;
      end
      fpu_ss_instr_pkg::FSW: begin
        is_store_o = 1'b1;
        op_select_o[1] = fpu_ss_pkg::RegB;
        use_fpu_o = 1'b0;
        rd_is_fp_dec = 1'b0;
      end
      default: begin
        use_fpu_o  = 1'b0;
        rd_is_fp_dec = 1'b0;
      end
    endcase
    // fix round mode for vectors and fp16alt
    if (set_dyn_rm_o) fpu_rnd_mode_o = fpu_rnd_mode_i;
  end
endmodule // fpu_ss_decoder
