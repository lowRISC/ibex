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
// FPU Subsystem Package
// Contributor: Moritz Imfeld <moimfeld@student.ethz.ch>

package fpu_ss_pkg;

  // ------------------------------
  // cv-x-if structs and parameters
  // ------------------------------

  parameter int          X_NUM_RS    = 3;
  parameter int          X_ID_WIDTH  = 4;
  parameter int          X_MEM_WIDTH = 32;
  parameter int          X_RFR_WIDTH = 32;
  parameter int          X_RFW_WIDTH = 32;
  parameter logic [31:0] X_MISA      = '0;
  parameter logic [ 1:0] X_ECS_XS    = '0;

  typedef struct packed {
    logic [          15:0] instr;
    logic [           1:0] mode;
    logic [X_ID_WIDTH-1:0] id;
  } x_compressed_req_t;

  typedef struct packed {
    logic [31:0] instr;
    logic        accept;
  } x_compressed_resp_t;

  typedef struct packed {
    logic                 [           31:0] instr;
    logic                 [            1:0] mode;
    logic                 [ X_ID_WIDTH-1:0] id;
    logic [  X_NUM_RS-1:0][X_RFR_WIDTH-1:0] rs;
    logic                 [   X_NUM_RS-1:0] rs_valid;
    logic                 [            5:0] ecs;
    logic                                   ecs_valid;
  } x_issue_req_t;

  typedef struct packed {
    logic accept;
    logic writeback;
    logic dualwrite;
    logic dualread;
    logic loadstore;
    logic ecswrite;
    logic exc;
  } x_issue_resp_t;

  typedef struct packed {
    logic [X_ID_WIDTH-1:0] id;
    logic                  commit_kill;
  } x_commit_t;

  typedef struct packed {
    logic [ X_ID_WIDTH-1:0]   id;
    logic [           31:0]   addr;
    logic [            1:0]   mode;
    logic                     we;
    logic [            2:0]   size;
    logic [X_MEM_WIDTH/8-1:0] be;
    logic [1:0]               attr;
    logic [X_MEM_WIDTH-1:0]   wdata;
    logic                     last;
    logic                     spec;
  } x_mem_req_t;

  typedef struct packed {
    logic       exc;
    logic [5:0] exccode;
    logic       dbg;
  } x_mem_resp_t;

    typedef struct packed {
    logic [ X_ID_WIDTH-1:0] id;
    logic [X_MEM_WIDTH-1:0] rdata;
    logic                   err;
    logic                   dbg;
  } x_mem_result_t;

  typedef struct packed {
    logic [    X_ID_WIDTH-1:0] id;
    logic [   X_RFW_WIDTH-1:0] data;
    logic [               4:0] rd;
    logic                      we;
    logic [               2:0] ecswe;
    logic [               5:0] ecsdata;
    logic                      exc;
    logic [               5:0] exccode;
    logic                      dbg;
    logic                      err;
  } x_result_t;

  // --------------
  // FPU_SS structs
  // --------------

  // Compressed predecoder request type
  typedef struct packed {
    logic [16:0] comp_instr;
  } comp_prd_req_t;

  // Compressed predecoder response type
  typedef struct packed {
    logic        accept;
    logic [32:0] decomp_instr;
  } comp_prd_rsp_t;

  // Predecoder request type
  typedef struct packed {
    logic [31:0] q_instr_data;
  } acc_prd_req_t;

  // Predecoder response type
  typedef struct packed {
    logic       p_accept;
    logic       p_is_mem_op;
    logic       p_writeback;
    logic [2:0] p_use_rs;
  } acc_prd_rsp_t;

  // Predecoder internal instruction metadata
  typedef struct packed {
    logic [31:0]  instr_data;
    logic [31:0]  instr_mask;
    acc_prd_rsp_t prd_rsp;
  } offload_instr_t;

  typedef enum logic [2:0] {
    None,
    AccBus,
    RegA,
    RegB,
    RegC,
    RegBRep,  // Replication for vectors
    RegDest
  } op_select_e;

  typedef enum logic [1:0] {
    Byte       = 2'b00,
    HalfWord   = 2'b01,
    Word       = 2'b10,
    DoubleWord = 2'b11
  } ls_size_e;

  typedef struct packed {
    logic [2:0][31:0] rs;
    logic [31:0]      instr_data;
    logic [3:0]       id;
    logic [1:0]       mode;
  } offloaded_data_t;

  typedef struct packed {
    logic [ 3:0] id;
    logic [ 4:0] rd;
    logic        we;
  } mem_metadata_t;

  typedef struct packed {
    logic [ 4:0] addr;
    logic        rd_is_fp;
    logic [ 3:0] id;
  } fpu_tag_t;

  // -----------
  // FPU Config
  // -----------

  // Floating-point extensions configuration
  parameter bit C_RVF = 1'b1;  // Is F extension enabled
  parameter bit C_RVD = 1'b0;  // Is D extension enabled - NOT SUPPORTED CURRENTLY

  // Transprecision floating-point extensions configuration
  parameter bit C_XF16 = 1'b0;  // Is half-precision float extension (Xf16) enabled
  parameter bit C_XF16ALT = 1'b0; // Is alternative half-precision float extension (Xf16alt) enabled
  parameter bit C_XF8 = 1'b0;  // Is quarter-precision float extension (Xf8) enabled
  parameter bit C_XFVEC = 1'b0;  // Is vectorial float extension (Xfvec) enabled

  // Latency of FP operations: 0 = no pipe registers, 1 = 1 pipe register etc.
  parameter int unsigned C_LAT_FP64 = 'd1; // set to 1 to mimic cv32e40p core internal
  parameter int unsigned C_LAT_FP32 = 'd1; // set to 1 to mimic cv32e40p core internal
  parameter int unsigned C_LAT_FP16 = 'd1; // set to 1 to mimic cv32e40p core internal
  parameter int unsigned C_LAT_FP16ALT = 'd1; // set to 1 to mimic cv32e40p core internal
  parameter int unsigned C_LAT_FP8 = 'd1; // set to 1 to break critical path
  parameter int unsigned C_LAT_DIVSQRT = 'd1;  // divsqrt post-processing pipe
  parameter int unsigned C_LAT_CONV = 'd1; // set to 1 to mimic cv32e40p core internal
  parameter int unsigned C_LAT_NONCOMP = 'd1; // set to 1 to mimic cv32e40p core internal

  // General FPU-specific defines

  // Length of widest floating-point format = width of fp regfile
  parameter C_FLEN = C_RVD ? 64 :  // D ext.
  C_RVF ? 32 :  // F ext.
  C_XF16 ? 16 :  // Xf16 ext.
  C_XF16ALT ? 16 :  // Xf16alt ext.
  C_XF8 ? 8 :  // Xf8 ext.
  0;  // Unused in case of no FP

  // Features (enabled formats, vectors etc.)
  parameter fpnew_pkg::fpu_features_t FPU_FEATURES = '{
  Width:         fpu_ss_pkg::C_FLEN,
  EnableVectors: fpu_ss_pkg::C_XFVEC,
  EnableNanBox:  1'b0,
  FpFmtMask:     {
    fpu_ss_pkg::C_RVF, fpu_ss_pkg::C_RVD, fpu_ss_pkg::C_XF16, fpu_ss_pkg::C_XF8, fpu_ss_pkg::C_XF16ALT
  }, IntFmtMask: {
    fpu_ss_pkg::C_XFVEC && fpu_ss_pkg::C_XF8, fpu_ss_pkg::C_XFVEC && (fpu_ss_pkg::C_XF16 || fpu_ss_pkg::C_XF16ALT), 1'b1, 1'b0
  }};

  // Implementation (number of registers etc)
  parameter fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
  PipeRegs:  '{// FP32, FP64, FP16, FP8, FP16alt
      '{
          fpu_ss_pkg::C_LAT_FP32, fpu_ss_pkg::C_LAT_FP64, fpu_ss_pkg::C_LAT_FP16, fpu_ss_pkg::C_LAT_FP8, fpu_ss_pkg::C_LAT_FP16ALT
      },  // ADDMUL
      '{default: fpu_ss_pkg::C_LAT_DIVSQRT},  // DIVSQRT
      '{default: fpu_ss_pkg::C_LAT_NONCOMP},  // NONCOMP
      '{default: fpu_ss_pkg::C_LAT_CONV}
  },  // CONV
  UnitTypes: '{
      '{default: fpnew_pkg::MERGED},  // ADDMUL
      '{default: fpnew_pkg::MERGED},  // DIVSQRT
      '{default: fpnew_pkg::PARALLEL},  // NONCOMP
      '{default: fpnew_pkg::MERGED}
  },  // CONV
  PipeConfig: fpnew_pkg::BEFORE};

endpackage // fpu_ss_pkg
