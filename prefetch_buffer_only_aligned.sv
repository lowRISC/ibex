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
// Description:    Prefetch buffer to only handle full or pairs of            //
//                 misaligned instructions to reduce area.                    //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "riscv_config.sv"


module riscv_prefetch_buffer_only_aligned
(
  input  logic        clk,
  input  logic        rst_n,

  // ID interface
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
  

  /// Regs
  enum logic [1:0] {IDLE, WAIT_GNT, WAIT_RVALID } CS, NS; // Will handle the steps for the memory interface


  logic [31:0]  fetch_addr_Q, fetch_addr_n; // The adress from the current fetch
  logic [31:0]  fetch_rdata_Q, fetch_rdata_n; // A 32 bit register to store current instruction if stalled
  logic         fetch_valid_Q, fetch_valid_n;

  /// Combinational signals
  logic [31:0]  addr_pc_next; // Calculate the next adress (adder as process counter)
  logic [31:0]  addr_mux; // The next address mux to be used
  logic [31:0]  instr_mux;

  logic addr_is_misaligned;
  logic instr_is_in_regs;
  logic instr_in_regs_is_compressed;

  enum logic [1:0] {FULL_INSTR_ALIGNED, C_INSTR_ALIGNED, C_INSTR_MISALIGNED} instruction_format;


  assign busy_o = (CS != IDLE) || instr_req_o;
  assign addr_is_misaligned = (fetch_addr_Q[1] == 1'b1); // Check if address is misaligned

  assign instr_is_in_regs = (fetch_valid_Q && addr_is_misaligned);

  assign instr_mux = fetch_valid_Q ? fetch_rdata_Q : instr_rdata_i;
  assign fetch_rdata_n = instr_mux;

  // Calculate next address. This is the actual PC of littleRISCV. Will use same adder instance for all cases
  always_comb
  begin
    unique case (instruction_format)
      FULL_INSTR_ALIGNED:             addr_pc_next = fetch_addr_Q + 32'h4;
      C_INSTR_ALIGNED:                addr_pc_next = fetch_addr_Q + 32'h2;
      C_INSTR_MISALIGNED:             addr_pc_next = fetch_addr_Q + 32'h2;
      default:                        addr_pc_next = fetch_addr_Q + 32'h4;
    endcase
  end

  // Construct the outgoing instruction
  always_comb
  begin
    unique case (instruction_format )
      FULL_INSTR_ALIGNED:             rdata_o = instr_mux;
      C_INSTR_ALIGNED:                rdata_o = {16'hxxxx, instr_mux[15:0]};
      C_INSTR_MISALIGNED:             rdata_o = {16'hxxxx, instr_mux[31:16]};
      default:                        rdata_o = instr_mux;
    endcase
  end



  always_comb
  begin
    NS = CS;

    fetch_addr_n = fetch_addr_Q;
    fetch_valid_n = fetch_valid_Q;

    valid_o = 1'b0;
    instr_req_o = 1'b0;
    instr_addr_o = {fetch_addr_Q[31:2], 2'b00};
    addr_mux = fetch_addr_Q;
    addr_o = fetch_addr_Q;

    instruction_format = FULL_INSTR_ALIGNED;

    unique case (CS)
      IDLE: begin

        if (branch_i) begin // If we have a branch condition, fetch from the new address
          fetch_valid_n = 1'b0;
          addr_mux = addr_i;
        end

        if (req_i) begin // Only proceed if ID wants to fetch new instructions
          // Check if we already buffered in cache
          if (~branch_i && instr_is_in_regs) begin
            // Assume it has to be a compressed instruction, as we only allow pairs of compressed instructions
            instruction_format = C_INSTR_MISALIGNED;
            addr_o = fetch_addr_Q;
            addr_mux = addr_pc_next;
            valid_o = 1'b1;

            if (ready_i) begin // Do not change state if ID is not ready
              fetch_addr_n = addr_mux;
              fetch_valid_n = 1'b0;
              NS = IDLE;
            end
          end
          
          // Else we have to fetch all instruction parts (aligned or misaligned in case of branch)
          else begin
            fetch_addr_n = addr_mux;
            fetch_valid_n = 1'b0;

            instr_req_o = 1'b1;
            instr_addr_o = {addr_mux[31:2], 2'b00};

            if (instr_gnt_i)
              NS = WAIT_RVALID;
            else
              NS = WAIT_GNT;
          end
        end
      end


      // Wait for grant of instruction memory
      WAIT_GNT: begin
        instr_req_o = 1'b1;
        instr_addr_o = {fetch_addr_Q[31:2], 2'b00};
        
        if (~branch_i) begin
          if (instr_gnt_i)
              NS = WAIT_RVALID;
          else
              NS = WAIT_GNT;
        end
        else begin // if branch_i
          fetch_valid_n = 1'b0;
          if (req_i) begin
            
            addr_mux = addr_i;
            fetch_addr_n = addr_mux;

            instr_req_o = 1'b1;
            instr_addr_o = {addr_mux[31:2], 2'b00};

            if (instr_gnt_i)
              NS = WAIT_RVALID;
            else
              NS = WAIT_GNT;
          end
          else
            NS = IDLE;
        end
      end


      WAIT_RVALID: begin
        if (~branch_i) begin
          
          NS = WAIT_RVALID;

          // Wait for valid data from instruction memory and proceed only if a new instruction is wanted OR if we were stalled.
          if (instr_rvalid_i | fetch_valid_Q) begin
            
            if (ready_i) begin
              fetch_valid_n = 1'b0;
            end
            else
              fetch_valid_n = 1'b1; // "Stall" fetch

            addr_mux = addr_pc_next;


            // If our wanted instruction address is aligned, we have fetched all parts needed.
            if (fetch_addr_Q[1] == 1'b0) begin 
              if (instr_mux[1:0] != 2'b11) begin // If compressed instruction
                instruction_format = C_INSTR_ALIGNED;
                addr_o = fetch_addr_Q;
                valid_o = 1'b1;

                if (ready_i) begin // Do not change state if ID is not ready
                  NS = IDLE; // Can go to IDLE as there is still a part of an instruction left to process in cache
                             // (and we do not want an unneccessary access if next instruction should be compressed as well)
                  fetch_addr_n = addr_mux; 
                  fetch_valid_n = 1'b1;
                end
              end

              else begin // If full instruction
                instruction_format = FULL_INSTR_ALIGNED;
                addr_o = fetch_addr_Q;
                valid_o = 1'b1;

                instr_addr_o = {addr_mux[31:2], 2'b00};

                if (ready_i) begin // Do not change state if ID is not ready
                  instr_req_o = 1'b1;
                  fetch_addr_n = addr_mux;

                  if (instr_gnt_i)
                    NS = WAIT_RVALID;
                  else
                    NS = WAIT_GNT;
                end
              end
            end
            
            else begin // If wanted instruction address is misaligned
                instruction_format = C_INSTR_MISALIGNED;
                addr_o = fetch_addr_Q;
                valid_o = 1'b1;
                
                if (ready_i) begin // Do not change state if ID is not ready
                  instr_req_o = 1'b1;
                  fetch_addr_n = addr_mux;
                  instr_addr_o = {addr_mux[31:2], 2'b00};

                  if (instr_gnt_i)
                    NS = WAIT_RVALID;
                  else
                    NS = WAIT_GNT;
                end
            end
          end
        end 

        else begin // if branch_i
          fetch_valid_n = 1'b0;
        
          if (req_i) begin
            
            addr_mux = addr_i;
            fetch_addr_n = addr_mux;

            instr_req_o = 1'b1;
            instr_addr_o = {addr_mux[31:2], 2'b00};

            if (instr_gnt_i)
              NS = WAIT_RVALID;
            else
              NS = WAIT_GNT;
          end
          else
            NS = IDLE;
        end
      end

      default: NS = IDLE;
    endcase;
  end



  //////////////////////////////////////////////////////////////////////////////
  // registers                                                                //
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      CS                      <= IDLE;
      fetch_addr_Q            <= 32'h0000;
      fetch_rdata_Q           <= 32'h0000;
      fetch_valid_Q           <= 1'b0;
    end  
    else begin
      CS                      <= NS;
      fetch_addr_Q            <= fetch_addr_n;
      fetch_rdata_Q           <= fetch_rdata_n;    
      fetch_valid_Q           <= fetch_valid_n;
    end
  end

endmodule
