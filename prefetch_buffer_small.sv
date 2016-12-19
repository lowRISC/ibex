// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Markus Wegmann - markus.wegmann@technokrat.ch              //
//                                                                            //
// Design Name:    Prefetcher Buffer for 32 bit memory interface              //
// Project Name:   littleRISCV                                                //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch buffer to cache 16 bit instruction part.          //
//                 Reduces gate count but might increase CPI.                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "riscv_config.sv"


module riscv_prefetch_buffer
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        req_i,

  input  logic        branch_i,
  input  logic [31:0] addr_i,

  input  logic        ready_i,
  output logic        valid_o,
  output logic [31:0] rdata_o,
  output logic [31:0] addr_o,

  // goes to instruction memory / instruction cache
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_rvalid_i,

  // Prefetch Buffer Status
  output logic        busy_o
);

  assign addr_o = addr_i; // Fix assignment, as no other adress is expected.
  
  enum logic [1:0] {IDLE, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED } CS, NS;

  logic [15:0]  last_instr_rdata_q; // A 16 bit register to store one compressed instruction for next fetch
  logic [31:2]  last_instr_addr_q; // A 16 bit register to store one compressed instruction for next fetch
  logic [15:0]  last_instr_rdata;
  logic [31:2]  last_instr_addr;

  logic         instr_is_compressed; // Shows if current instruction fetch is compressed
  logic         instr_is_misaligned;
  logic         instr_part_in_fifo; // Indicates if address (mod 4) is already fetched.
  logic         instr_part_in_fifo_is_compressed;


  assign last_instr_rdata = instr_rdata_i[31:16]; // Throw away lower part to keep instruction register at 16 bit
  assign last_instr_addr = addr_i[31:2];

  assign instr_is_compressed = (instr_rdata_i[1:0] != 2'b11); // Check if instruction is not a 32 bit instruction and therefore compressed
  assign instr_addr_is_misaligned = (instr_addr_o[1] == 1'b1); // Check if address is (addr/2 mod 2) == 1

  assign instr_part_in_fifo = ( (addr_i[31:2] == last_instr_addr_q) && instr_addr_is_misaligned ); // Check if (address / 4) is the same and 
  assign instr_part_in_fifo_is_compressed = (last_instr_rdata_q[1:0] != 2'b11);


  enum logic []

  enum logic [1:0] {INSTR_ALIGNED, C_INSTR_MISALIGNED, C_INSTR_IN_REG, PART_INSTR_IN_REG} instruction_format;

  // Construct the outgoing instruction
  always_comb
  begin
    unique case (instruction_format)
      INSTR_ALIGNED:      rdata_o = instr_rdata_i;
      C_INSTR_MISALIGNED: rdata_o = {16'h0000, instr_rdata_i[15:0]};
      C_INSTR_IN_REG:     rdata_o = {16'h0000, last_instr_rdata};
      PART_INSTR_IN_REG:  rdata_o = {instr_rdata_i[15:0], last_instr_rdata};
      default:            rdata_o = instr_rdata_i;
    endcase
  end




  always_comb
  begin
    NS = CS;

    valid_o = 1'b1;
    instr_req_o = 1'b0;
    instr_addr_o = 1'b0;

    busy_o = 1'b0;


    unique case (CS)
      case IDLE:
        if (req_i == 1'b1)
        begin


        end
      case 

      default: NS = IDLE;

    end
  
  end



  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      CS              <= IDLE;
      instr_reg_q     <= 32'h0000;
    end
    else
    begin
      CS              <= NS;
    end
  end

endmodule
