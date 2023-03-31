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
// Floating-point CSR
// Contributor: Moritz Imfeld <moimfeld@student.ethz.ch>

module fpu_ss_csr (
    input logic clk_i,
    input logic rst_ni,

    input  logic               [31:0] instr_i,
    input  logic               [31:0] csr_data_i,
    input  fpnew_pkg::status_t        fpu_status_i,
    input  logic                      in_buf_pop_valid_i,
    input  logic                      fpu_out_valid_i,
    input  logic               [ 3:0] csr_id_i,
    output logic               [31:0] csr_rdata_o,
    output logic               [ 2:0] frm_o,
    output logic                      csr_wb_o,
    output logic               [ 4:0] csr_wb_addr_o,
    output logic               [ 3:0] csr_wb_id_o,
    output logic                      csr_instr_o,
    output logic                      csr_instr_rec_o

);

  logic [31:0] fcsr_d, fcsr_q, instr_q;

  assign frm_o = fcsr_q[7:5];
  assign csr_wb_addr_o = instr_q[11:7];

  always_ff @(posedge clk_i, negedge rst_ni) begin : proc_instr_q
    if(~rst_ni) begin
      instr_q <= '0;
      csr_wb_id_o <= '0;
    end else begin
      if (in_buf_pop_valid_i) begin
        csr_wb_id_o <= csr_id_i;
        instr_q <= instr_i;
      end else begin
        instr_q <= '0;
      end
    end
  end

  always_comb begin
    fcsr_d      = fcsr_q;
    csr_wb_o    = 1'b0;
    csr_rdata_o = '0;
    csr_instr_o = 1'b1;
    unique casez (instr_q)
      fpu_ss_instr_pkg::CSRRW_FSCSR: begin  // Swap value in fcsr with the one in rs1
        fcsr_d      = csr_data_i;
        csr_wb_o    = 1'b1;
        csr_rdata_o = fcsr_q;
      end
      fpu_ss_instr_pkg::CSRRS_FRCSR: begin  // Read value from fcsr and copy to int reg
        csr_wb_o    = 1'b1;
        csr_rdata_o = fcsr_q;
      end
      fpu_ss_instr_pkg::CSRRW_FSRM: begin  // Swap frm value in fcsr with the one in rs1
        fcsr_d[7:5] = csr_data_i[2:0];
        csr_wb_o    = 1'b1;
        csr_rdata_o = {29'b0, fcsr_q[7:5]};
      end
      fpu_ss_instr_pkg::CSRRS_FRRM: begin // Read frm from fcsr and copy to int reg (zeropadding at the front)
        csr_wb_o    = 1'b1;
        csr_rdata_o = {29'b0, fcsr_q[7:5]};
      end
      fpu_ss_instr_pkg::CSRRWI_FSRMI: begin // Swap frm value in fcsr with the one in the immediat instr_i [17:15] (immediat is at [19:15])
        fcsr_d[7:5] = instr_i[17:15];
      end
      fpu_ss_instr_pkg::CSRRW_FSFLAGS: begin  // Swap fflags value in fcsr with the one in rs1
        fcsr_d[4:0] = csr_data_i[4:0];
        csr_wb_o    = 1'b1;
        csr_rdata_o = {27'b0, fcsr_q[4:0]};
      end
      fpu_ss_instr_pkg::CSRRS_FRFLAGS: begin // Read fflags from fcsr and copy to int reg (zeropadding at the front)
        csr_wb_o    = 1'b1;
        csr_rdata_o = {27'b0, fcsr_q[4:0]};
      end
      fpu_ss_instr_pkg::CSRRWI_FSFLAGSI: begin // Swap frm value in fcsr with the one in the immediat instr_i [19:15] (immediat is at [19:15])
        fcsr_d[4:0] = instr_i[19:15];
      end
      default: begin
        if (fpu_out_valid_i) begin
          fcsr_d = {
            fcsr_q[31:5],
            fpu_status_i.NV,
            fpu_status_i.DZ,
            fpu_status_i.OF,
            fpu_status_i.UF,
            fpu_status_i.NX
          };
        end else begin
          fcsr_d = fcsr_q;
        end
        csr_wb_o = 1'b0;
        csr_rdata_o = '0;
        csr_instr_o = 1'b0;
      end
    endcase
  end

  always_comb begin
    csr_instr_rec_o = 1'b0;
    if (in_buf_pop_valid_i) begin
      unique casez (instr_i)
        fpu_ss_instr_pkg::CSRRW_FSCSR,  // Swap value in fcsr with the one in rs1
        fpu_ss_instr_pkg::CSRRS_FRCSR,  // Read value from fcsr and copy to int reg
        fpu_ss_instr_pkg::CSRRW_FSRM,  // Swap frm value in fcsr with the one in rs1
        fpu_ss_instr_pkg::CSRRS_FRRM, // Read frm from fcsr and copy to int reg (zeropadding at the front)
        fpu_ss_instr_pkg::CSRRWI_FSRMI, // Swap frm value in fcsr with the one in the immediat instr_i [17:15] (immediat is at [19:15])
        fpu_ss_instr_pkg::CSRRW_FSFLAGS,  // Swap fflags value in fcsr with the one in rs1
        fpu_ss_instr_pkg::CSRRS_FRFLAGS, // Read fflags from fcsr and copy to int reg (zeropadding at the front)
        fpu_ss_instr_pkg::CSRRWI_FSFLAGSI: begin // Swap frm value in fcsr with the one in the immediat instr_i [19:15] (immediat is at [19:15])
          csr_instr_rec_o = 1'b1;
        end
        default:;
      endcase
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      fcsr_q <= '0;
    end else begin
      fcsr_q <= fcsr_d;
    end
  end

endmodule // fpu_ss_csr
