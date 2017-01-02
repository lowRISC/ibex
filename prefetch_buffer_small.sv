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


module riscv_prefetch_buffer_small
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
  enum logic [1:0] {IDLE, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED } CS, NS; // Will handle the steps for the memory interface


  logic [31:0]  fetch_addr_Q, fetch_addr_n; // The adress from the current fetch
  logic [15:0]  last_fetch_rdata_Q, last_fetch_rdata_n; // A 16 bit register to store one compressed instruction or half of a full instruction for next fetch
  logic [31:0]  current_fetch_rdata_Q, current_fetch_rdata_n; // A 32 bit register to store full instruction when valid fetch was stalled. Reduces memory accesses

  logic         last_fetch_valid_Q, last_fetch_valid_n; // Fetch was stalled so we need instruction word in register
  logic         last_addr_misaligned_Q, last_addr_misaligned_n; // Indicates whether we need to fetch the second part of an misaligned full instruction
  logic         fetch_stalled_Q, fetch_stalled_n; // Current fetch is stalled and we need to store full 32 bit instruction to memory to reduce memory accesses

  logic [31:0]  last_fetch_addr_Q, last_fetch_addr_n; // The adress from the last fetch



  /// Combinational signals
  logic [31:0]  addr_pc_next; // Calculate the next adress (adder as process counter)
  logic [31:0]  addr_mux; // The next address mux to be used

  logic [31:0]  instr_mux;

  logic addr_is_misaligned;
  logic instr_is_in_regs; // Indicates if address mod 4 is already fetched. 
  //                         It is implicitely assumed that the fetch is consecutive to the last fetch to spare a comparator.
  //                         In the other case we devalidate the cache which we check.
  logic instr_in_regs_is_compressed;


  enum logic [2:0] {FULL_INSTR_ALIGNED, C_INSTR_ALIGNED_DIRECT, C_INSTR_MISALIGNED_DIRECT, C_INSTR_IN_REG_OR_FIRST_FETCH, INSTR_IN_REG} instruction_format;
  //                        upper lower
  // FULL_INSTR_ALIGNED:  [ iiii, iiii] from mem
  // C_INSTR_DIRECT:      [ xxxx, iiii] from mem
  // C_INSTR_IN_REG:      [ iiii, xxxx] from reg
  // INSTR_IN_REG:        [ iiii, xxxx] 1st part in reg
  //                      [ xxxx, iiii] 2nd part from mem


  assign busy_o = (CS != IDLE) || instr_req_o;

  assign addr_is_misaligned = (fetch_addr_Q[1] == 1'b1); // Check if address is misaligned

  assign instr_is_in_regs = ( last_fetch_valid_Q && addr_is_misaligned);
  assign instr_in_regs_is_compressed = (last_fetch_rdata_Q[1:0] != 2'b11); // Upper half is compressed instruction

  assign instr_mux = fetch_stalled_Q ? current_fetch_rdata_Q : instr_rdata_i;

  // Calculate next address. This is the actual PC of littleRISCV. Will use same adder instance for all cases
  always_comb
  begin
    unique case (instruction_format)
      FULL_INSTR_ALIGNED:             addr_pc_next = fetch_addr_Q + 32'h4;
      C_INSTR_ALIGNED_DIRECT:         addr_pc_next = fetch_addr_Q + 32'h2;
      C_INSTR_MISALIGNED_DIRECT:      addr_pc_next = fetch_addr_Q + 32'h2;
      C_INSTR_IN_REG_OR_FIRST_FETCH:  addr_pc_next = fetch_addr_Q + 32'h2;
      INSTR_IN_REG:                   addr_pc_next = fetch_addr_Q + 32'h2;
      default:                        addr_pc_next = fetch_addr_Q + 32'h4;
    endcase
  end

  // Construct the outgoing instruction
  always_comb
  begin
    unique case (instruction_format )
      FULL_INSTR_ALIGNED:             rdata_o = instr_mux;
      C_INSTR_ALIGNED_DIRECT:         rdata_o = {16'hxxxx, instr_mux[15:0]};
      C_INSTR_MISALIGNED_DIRECT:      rdata_o = {16'hxxxx, instr_mux[31:16]};
      C_INSTR_IN_REG_OR_FIRST_FETCH:  rdata_o = {16'hxxxx, last_fetch_rdata_Q};
      INSTR_IN_REG:                   rdata_o = {instr_mux[15:0], last_fetch_rdata_Q};
      default:                        rdata_o = instr_mux;
    endcase
  end



  always_comb
  begin
    NS = CS;

    fetch_addr_n = fetch_addr_Q;
    last_fetch_addr_n = last_fetch_addr_Q;
    last_fetch_rdata_n = last_fetch_rdata_Q;
    last_fetch_valid_n = last_fetch_valid_Q;
    last_addr_misaligned_n = last_addr_misaligned_Q;
    fetch_stalled_n = fetch_stalled_Q;

    valid_o = 1'b0;
    instr_req_o = 1'b0;
    instr_addr_o = {fetch_addr_Q[31:2], 2'b00};
    addr_mux = fetch_addr_Q;
    addr_o = fetch_addr_Q;

    instruction_format = FULL_INSTR_ALIGNED;


    unique case (CS)
      IDLE: begin
        last_addr_misaligned_n = 1'b0;
        fetch_stalled_n = 1'b0;

        if (branch_i) begin // If we have a branch condition, fetch from the new address
          last_fetch_valid_n = 1'b0;
          addr_mux = addr_i;
        end

        if (req_i) begin // Only proceed if ID wants to fetch new instructions
          // Check if we already buffered in cache
          if (~branch_i && instr_is_in_regs) begin
            // Check if we already have a compressed instruction in cache
            if (instr_in_regs_is_compressed) begin
              instruction_format = C_INSTR_IN_REG_OR_FIRST_FETCH;
              addr_o = fetch_addr_Q;
              addr_mux = addr_pc_next;
              valid_o = 1'b1;

              if (ready_i) begin // Do not change state if ID is not ready
                fetch_addr_n = addr_mux;
                NS = IDLE;
              end
            end

            // Else we already buffered one misaligned half of an overlaping instruction
            // We need to fetch the other part in the next cycle
            else begin
              instruction_format = C_INSTR_IN_REG_OR_FIRST_FETCH; 
              last_addr_misaligned_n = 1'b1;
              last_fetch_addr_n = fetch_addr_Q; // Save address to restore it when we need to output instruction address
              addr_mux = addr_pc_next;
              fetch_addr_n = addr_mux;
              
              instr_req_o = 1'b1;
              instr_addr_o = {addr_mux[31:2], 2'b00};

              if (instr_gnt_i)
                NS = WAIT_RVALID;
              else
                NS = WAIT_GNT;
            end
          end
          
          // Else we have to fetch all instruction parts (aligned or misaligned in case of branch)
          else begin
            fetch_addr_n = addr_mux;

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
          last_fetch_valid_n = 1'b0;
          if (instr_rvalid_i) begin
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
          else
            NS = WAIT_ABORTED;
        end
      end


      WAIT_RVALID: begin
        if (~branch_i) begin
          
          NS = WAIT_RVALID;

          // Wait for valid data from instruction memory and proceed only if a new instruction is wanted OR if we were stalled.
          if (instr_rvalid_i | fetch_stalled_Q) begin
            

            if (ready_i) begin // Do not alter registers if ID is not ready
              // Regs
              last_fetch_rdata_n = instr_mux[31:16];
              last_fetch_valid_n = 1'b1;
              last_addr_misaligned_n = 1'b0;
              fetch_stalled_n = 1'b0;
            end
            else
              fetch_stalled_n = 1'b1; // Stall fetch

            addr_mux = addr_pc_next;

            // If our last access to the instruction memory was fetching the first part, we now have fetched the second part and can output it
            if (last_addr_misaligned_Q) begin
              instruction_format = INSTR_IN_REG;
              addr_o = last_fetch_addr_Q;
              valid_o = 1'b1;

              if (ready_i) begin // Do not change state if ID is not ready
                NS = IDLE; // Can go to IDLE as there is still a part of an instruction left to process in cache 
                           // (and we do not want an unneccessary access if next instruction should be compressed)
                fetch_addr_n = addr_mux;
              end
            end

            // If our wanted instruction address is aligned, we have fetched all parts needed.
            else if (fetch_addr_Q[1] == 1'b0) begin 
              if (instr_mux[1:0] != 2'b11) begin // If compressed instruction
                instruction_format = C_INSTR_ALIGNED_DIRECT;
                addr_o = fetch_addr_Q;
                valid_o = 1'b1;

                if (ready_i) begin // Do not change state if ID is not ready
                  NS = IDLE; // Can go to IDLE as there is still a part of an instruction left to process in cache
                             // (and we do not want an unneccessary access if next instruction should be compressed as well)
                  fetch_addr_n = addr_mux; 
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
              if (instr_mux[17:16] != 2'b11) begin // If compressed instruction
              
                instruction_format = C_INSTR_MISALIGNED_DIRECT;
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

              else begin // Else we a have a full 32-bit instruction which is overlapping two words in memory
                // Even if ~ready_i, we can proceed to fetch second half of a full instruction, as we do not output new data to IF
                instruction_format = C_INSTR_IN_REG_OR_FIRST_FETCH;

                fetch_addr_n = addr_mux;
                last_fetch_rdata_n = instr_mux[31:16];
                last_fetch_valid_n = 1'b1;
                last_addr_misaligned_n = 1'b1;
                fetch_stalled_n = 1'b0;
                last_fetch_addr_n = fetch_addr_Q; // Save address to restore it when we need to output instruction address

                
                instr_req_o = 1'b1;
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
          last_fetch_valid_n = 1'b0;
          last_addr_misaligned_n = 1'b0;
          fetch_stalled_n = 1'b0;
          
          if (instr_rvalid_i) begin
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
          else
            NS = WAIT_ABORTED;
        end
      end


      // Wait for rvalid to finish latest access accordingly
      WAIT_ABORTED: begin
        if (instr_rvalid_i) begin
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
        else begin
          NS = WAIT_ABORTED;
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
      last_fetch_addr_Q       <= 32'h0000;
      current_fetch_rdata_Q   <= 32'h0000;
      last_fetch_rdata_Q      <= 16'h00;
      last_fetch_valid_Q      <= 1'b0;
      last_addr_misaligned_Q  <= 1'b0;
      fetch_stalled_Q         <= 1'b0;

    end  
    else begin
      CS                      <= NS;

      fetch_addr_Q            <= fetch_addr_n;
      last_fetch_addr_Q       <= last_fetch_addr_n;
      current_fetch_rdata_Q   <= current_fetch_rdata_n;
      last_fetch_rdata_Q      <= last_fetch_rdata_n;
      last_fetch_valid_Q      <= last_fetch_valid_n;
      last_addr_misaligned_Q  <= last_addr_misaligned_n;
      fetch_stalled_Q         <= fetch_stalled_n;
    end
  end

endmodule
