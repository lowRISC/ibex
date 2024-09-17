// Copyleft 2024
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * ISOLDE Custom Instruction decoder
 *
 */

`include "prim_assert.sv"

module isolde_decoder #(

) (
    input logic clk_i,
    input logic rst_ni,

    // to/from controller
    input  logic [4:0][31:0] isolde_decoder_instr_batch_i,    // from IF-ID pipeline registers
    input  logic             isolde_decoder_enable_i,         // illegal instr encountered
    output logic             isolde_decoder_illegal_instr_o,  // illegal instr encountered
    output logic             isolde_decoder_busy_o


);

  // FSM states
  typedef enum logic [1:0] {
    BOOT,
    IDLE,
    FETCH_COMPUTE,
    FETCH_REST     // Fetch the remaining words for multi-word instructions
  } state_t;

  state_t idvli_state, idvli_next;
  logic [6:0] opCode;
  logic [2:0] nnn;  // Encodes bits 14-12
  // Define constants for custom encodings
  localparam logic [6:0] RISCV_ENC_GE80 = 7'b1111111;  // Custom opcode for GE80 (160-bit or 96-bit instructions)
  localparam logic [6:0] RISCV_ENC_64   = 7'b0111111;  // Custom opcode for 64-bit instruction (2 words)

  localparam logic [2:0] RISCV_ENC_GE80_N5 = 3'h5;  // Custom encoding for N5 (5 words)
  localparam logic [2:0] RISCV_ENC_GE80_N1 = 3'h1;  // Custom encoding for N1 (3 words)
  // Extract opcode and nnn
  assign opCode = isolde_decoder_instr_batch_i[0][6:0];     // Extracting opcode bits
  assign nnn    = isolde_decoder_instr_batch_i[0][14:12];   // Extracting bits [14:12] for nnn
  logic [2:0] vlen_instr_words;  // Instruction length in words
  logic [2:0] read_ptr;  // Instruction length in words

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      idvli_state <= BOOT;
      read_ptr <= 0;
      isolde_decoder_illegal_instr_o <= 0;
      //isolde_decoder_busy_o <= 0;
    end else begin
      idvli_state <= idvli_next;
      case (idvli_next)
        BOOT: begin
          read_ptr <= read_ptr + 1;
        end
        IDLE: begin
          isolde_decoder_illegal_instr_o <= 0;
          //isolde_decoder_busy_o <= 0;
        end
        FETCH_COMPUTE: begin
          read_ptr <= 1;
          // isolde_decoder_busy_o <= 1;
          case (opCode)
            RISCV_ENC_GE80: begin
              if (nnn == RISCV_ENC_GE80_N5) begin
                vlen_instr_words <= 5;  // 5-word instruction (160 bits)
              end else if (nnn == RISCV_ENC_GE80_N1) begin
                vlen_instr_words <= 3;  // 3-word instruction (96 bits)
              end else begin
                // Assert if unknown nnn is encountered
                $display("Unsupported custom instruction: nnn = %0d", nnn);
                isolde_decoder_illegal_instr_o <= 1;
              end
            end
            RISCV_ENC_64: begin
              vlen_instr_words <= 2;  // 2-word instruction (64 bits)
            end
            default: isolde_decoder_illegal_instr_o <= 1;
          endcase
        end
        FETCH_REST: begin
          read_ptr <= read_ptr + 1;
        end
      endcase
    end
  end

  always_comb begin
    // idvli_next = IDLE;  //loop back
    case (idvli_state)
      BOOT:
      if (read_ptr == 3'h6) begin
        idvli_next = IDLE;
        isolde_decoder_busy_o = 0;
      end
      IDLE:
      if (isolde_decoder_enable_i) begin
        idvli_next = FETCH_COMPUTE;
        isolde_decoder_busy_o = 1;
      end
      FETCH_COMPUTE: idvli_next = FETCH_REST;
      FETCH_REST: begin
        if (vlen_instr_words == read_ptr) begin
          isolde_decoder_busy_o = 0;
          idvli_next = IDLE;
        end
      end
    endcase
  end
endmodule
