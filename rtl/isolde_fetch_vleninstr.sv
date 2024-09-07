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
  input  logic        valid_i,               // signals that instr_i can be used
  input  logic [31:0] instr_i,               // instruction input from icache
  output logic [4:0][31:0] vlen_instr_o,     // in-order succession of maximum 5 instr_i
  output logic [2:0]  vlen_inst_words_o,     // instruction length in words
  output logic        vlen_instr_ready_o     // vlen_instr_o is ready to use
);

  // FSM states
  typedef enum logic [1:0] {
    IDLE,
    COMPUTE_FETCH,   // Compute the instruction length and fetch the first word
    FETCH_REST,      // Fetch the remaining words
    READY            // All instruction words fetched and ready to output
  } state_t;

  state_t state, next_state;

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
  logic        fetching_done;       // Indicates when all words are fetched
  logic [31:0] instr_reg;           // Register to hold the instruction input

  // Extract opcode and nnn
  assign opCode = instr_i[6:0];     // Extracting opcode bits
  assign nnn    = instr_i[14:12];   // Extracting bits [14:12] for nnn

  // FSM state transitions
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

  // FSM next state logic
  always_comb begin
    case (state)
      IDLE: begin
        if (valid_i) begin
          next_state = COMPUTE_FETCH;  // Move to compute and fetch state when valid_i is asserted
        end else begin
          next_state = IDLE;
        end
      end

      COMPUTE_FETCH: begin
        next_state = (fetch_words > 1) ? FETCH_REST : READY;  // If more than 1 word, fetch rest
      end

      FETCH_REST: begin
        next_state = (wr_ptr == fetch_words) ? READY : FETCH_REST;  // Transition to READY when done fetching
      end

      READY: begin
        next_state = IDLE;  // Go back to IDLE after output is ready
      end

      default: begin
        next_state = IDLE;
      end
    endcase
  end

  // FSM outputs and control logic
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wr_ptr <= 0;
      vlen_inst_words_o <= 0;
      fetching_done <= 0;
      vlen_instr_ready_o <= 0;
    end else begin
      case (state)
        IDLE: begin
          wr_ptr <= 0;
          vlen_inst_words_o <= 0;
          fetching_done <= 0;
          vlen_instr_ready_o <= 0;
        end

        COMPUTE_FETCH: begin
          // Compute instruction length and store the first word
          vlen_instr_o[0] <= instr_i;  // First word fetched immediately
          wr_ptr <= 1;

          // Determine instruction length based on opCode and nnn
          case (opCode)
            RISCV_ENC_GE80: begin
              if (nnn == RISCV_ENC_GE80_N5) begin
                vlen_inst_words_o <= 5;  // 5-word instruction (160 bits)
              end else if (nnn == RISCV_ENC_GE80_N1) begin
                vlen_inst_words_o <= 3;  // 3-word instruction (96 bits)
              end else begin
                vlen_inst_words_o <= 1;  // Default case (1-word instruction)
              end
            end

            RISCV_ENC_64: begin
              vlen_inst_words_o <= 2;  // 2-word instruction (64 bits)
            end

            default: begin
              vlen_inst_words_o <= 1;  // Default single word instruction (32 bits)
            end
          endcase

          // Set number of words to fetch
          fetch_words <= vlen_inst_words_o;
        end

        FETCH_REST: begin
          // Fetch the remaining instruction words (if any)
          if (wr_ptr < fetch_words) begin
            vlen_instr_o[wr_ptr] <= instr_i;  // Store directly into vlen_instr_o
            wr_ptr <= wr_ptr + 1;
          end

          if (wr_ptr == fetch_words) begin
            fetching_done <= 1;
            vlen_instr_ready_o <= 1;
          end
        end

        READY: begin
          // Set ready flag indicating that the instruction is ready
          vlen_instr_ready_o <= 1;  // Output is ready
        end

      endcase
    end
  end

endmodule
