// Copyleft
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Fetch variable length instruction
 *
 * Decodes RISC-V variable lenght encoded instructions 
 */

`include "prim_assert.sv"

module isolde_fetch_vleninstr (
  input  logic        clk_i,
  input  logic        rst_ni,
  input  logic        valid_i,               // Signals that zz_instr_i can be used
  input  logic [31:0] zz_instr_i,               // Instruction input from icache
  output logic [4:0][31:0] vlen_instr_o,     // In-order succession of maximum 5 zz_instr_i
  output logic [2:0]  vlen_instr_words_o,     // Instruction length in words
  output logic        vlen_instr_ready_o     // vlen_instr_o is ready to use
);

  // FSM states
  typedef enum logic [1:0] {
    IDLE,
    FETCH_REST      // Fetch the remaining words for multi-word instructions
  } state_t;

  state_t state;

  // Extract the opcode and nnn fields from the instruction
  logic [6:0] opCode;
  logic [2:0] nnn;  // Encodes bits 14-12

  // Define constants for custom encodings
  localparam logic [6:0] RISCV_ENC_GE80 = 7'b1111111;  // Custom opcode for GE80 (160-bit or 96-bit instructions)
  localparam logic [6:0] RISCV_ENC_64   = 7'b0111111;  // Custom opcode for 64-bit instruction (2 words)

  localparam logic [2:0] RISCV_ENC_GE80_N5 = 3'h5;     // Custom encoding for N5 (5 words)
  localparam logic [2:0] RISCV_ENC_GE80_N1 = 3'h1;     // Custom encoding for N1 (3 words)

  // Internal control signals
  logic [2:0] fetch_words;         // Number of words to fetch based on instruction length
  logic [2:0] wr_ptr;              // Write pointer to store fetched words into vlen_instr_o
  

  // Extract opcode and nnn
  assign opCode = zz_instr_i[6:0];     // Extracting opcode bits
  assign nnn    = zz_instr_i[14:12];   // Extracting bits [14:12] for nnn



  // FSM outputs and control logic
  always_ff @(posedge clk_i ) begin
    if (!rst_ni) begin
      state = IDLE;
      wr_ptr = 0;
      vlen_instr_words_o = 0;
      vlen_instr_ready_o = 0;
      vlen_instr_o[0]=0;
    end else begin
      
      case (state)
        IDLE: begin
          wr_ptr = 1;
         if (valid_i) begin
            //store the first word
            vlen_instr_o[0] = zz_instr_i;  // First word fetched immediately

            //compute instruction length based on opCode and nnn
            case (opCode)
              RISCV_ENC_GE80: begin
                if (nnn == RISCV_ENC_GE80_N5) begin
                  vlen_instr_words_o = 5;  // 5-word instruction (160 bits)
                end else if (nnn == RISCV_ENC_GE80_N1) begin
                  vlen_instr_words_o = 3;  // 3-word instruction (96 bits)
                end else begin
                  // Assert if unknown nnn is encountered
                  $fatal("Unsupported custom instruction: nnn = %0d", nnn);
                end
                state = FETCH_REST;
              end

              RISCV_ENC_64: begin
                vlen_instr_words_o = 2;  // 2-word instruction (64 bits)
                state = FETCH_REST;
              end

              default: begin
                // Single-word instruction (32 bits)
                vlen_instr_words_o = 1;
                vlen_instr_ready_o = 1;  // Set ready immediately for single-word instruction
              end
            endcase
          end
        end

        FETCH_REST: begin
          // Only fetch when valid_i is asserted
          if (valid_i) begin
            // Continue fetching multi-word instructions
            if (wr_ptr < vlen_instr_words_o) begin
              vlen_instr_o[wr_ptr] = zz_instr_i;
              if (wr_ptr == vlen_instr_words_o ) begin
                vlen_instr_ready_o = 1;  // Instruction is ready when all words are fetched
                state = IDLE;
              end else begin
                wr_ptr = wr_ptr + 1;
              end
          end
        end
        end

      endcase
   end
  end

endmodule
