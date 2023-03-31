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
// FPU Subsystem Compressed Instruction Predecoder
// Moritz Imfeld <moimfeld@student.eth.ch>

module fpu_ss_compressed_predecoder
    import fpu_ss_pkg::*;
  (
    input  fpu_ss_pkg::comp_prd_req_t prd_req_i,
    output fpu_ss_pkg::comp_prd_rsp_t prd_rsp_o
);

  always_comb begin
    prd_rsp_o.accept = 1'b0;
    prd_rsp_o.decomp_instr = '0;

    unique casez (prd_req_i.comp_instr)
      fpu_ss_instr_pkg::C_FLW: begin
        prd_rsp_o.accept = 1'b1;
        prd_rsp_o.decomp_instr = { 5'b0, prd_req_i.comp_instr[5], prd_req_i.comp_instr[12:10], prd_req_i.comp_instr[6], 2'b00, 2'b01, prd_req_i.comp_instr[9:7], 3'b010, 2'b01, prd_req_i.comp_instr[4:2], 7'b000_0111 };
      end
      fpu_ss_instr_pkg::C_FLWSP: begin
        prd_rsp_o.accept = 1'b1;
        prd_rsp_o.decomp_instr = { 4'b0, prd_req_i.comp_instr[3:2], prd_req_i.comp_instr[12], prd_req_i.comp_instr[6:4], 2'b00, 5'h02, 3'b010, prd_req_i.comp_instr[11:7], 7'b000_0111 };
      end
      fpu_ss_instr_pkg::C_FSW: begin
        prd_rsp_o.accept = 1'b1;
        prd_rsp_o.decomp_instr = { 5'b0, prd_req_i.comp_instr[5], prd_req_i.comp_instr[12], 2'b01, prd_req_i.comp_instr[4:2], 2'b01, prd_req_i.comp_instr[9:7], 3'b010, prd_req_i.comp_instr[11:10], prd_req_i.comp_instr[6], 2'b00, 7'b010_0111 };
      end
      fpu_ss_instr_pkg::C_FSWSP: begin
        prd_rsp_o.accept = 1'b1;
        prd_rsp_o.decomp_instr = { 4'b0, prd_req_i.comp_instr[8:7], prd_req_i.comp_instr[12], prd_req_i.comp_instr[6:2], 5'h02, 3'b010, prd_req_i.comp_instr[11:9], 2'b00, 7'b010_0111 };
      end
      default: begin
        prd_rsp_o.accept = 1'b0;
        prd_rsp_o.decomp_instr = '0;
      end
    endcase
  end
endmodule // fpu_ss_compressed_predecoder
