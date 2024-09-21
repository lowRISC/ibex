// Copyleft 2024
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * ISOLDE Custom Instruction decoder
 *
 */

`include "prim_assert.sv"



module isolde_decoder
  import isolde_register_file_pkg::RegDataWidth, isolde_register_file_pkg::RegCount, isolde_register_file_pkg::RegSize, isolde_register_file_pkg::RegAddrWidth;
  import isolde_decoder_pkg::*;
#(

) (
    input logic clk_i,
    input logic rst_ni,

    // to/from controller
    input  logic [4:0][31:0] isolde_decoder_instr_batch_i,    // from IF-ID pipeline registers
    input  logic             isolde_decoder_enable_i,         // illegal instr encountered
    output logic             isolde_decoder_illegal_instr_o,  // illegal instr encountered
    output logic             isolde_decoder_busy_o,

    //ISOLDE Register file interface
    output logic [RegAddrWidth-1:0] isolde_decoder_rf_raddr_a_o,  //  Read port A address output
    input logic [RegSize-1:0][RegDataWidth-1:0] isolde_decoder_rf_rdata_a_i,  //  Read port A data input
    output logic [RegAddrWidth-1:0] isolde_decoder_rf_waddr_a_o,  // Write port W1 address output
    output logic [RegSize-1:0][RegDataWidth-1:0] isolde_decoder_rf_wdata_a_o,  // Write port W1 data output
    output logic isolde_decoder_rf_we_a_o,  // Write port W1 enable signal
    input logic isolde_decoder_rf_err_i  // Combined error signal for invalid reads/writes
);

  // FSM states
  typedef enum logic [1:0] {
    BOOT,
    IDLE,
    FETCH_COMPUTE,
    FETCH_REST     // Fetch the remaining words for multi-word instructions
  } state_t;

  state_t idvli_state, idvli_next;
  logic [4:0] rd;
  logic [6:0] func7;
  isolde_opcode_e isolde_opcode_d, isolde_opcode_q;

  logic [2:0] vlen_instr_words_d, vlen_instr_words_q;  // Instruction length in words
  logic [2:0] read_ptr;


  always_comb begin
    decode_isolde_opcode(isolde_decoder_instr_batch_i[0][6:0],  //opcode
                         isolde_decoder_instr_batch_i[0][14:12],  //nnn
                         isolde_decoder_instr_batch_i[0][31:25],  //func7
                         isolde_opcode_d, vlen_instr_words_d);
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      idvli_state <= BOOT;
      read_ptr <= 0;
      isolde_decoder_illegal_instr_o <= 0;
      isolde_decoder_rf_we_a_o <= 1'b0;
      //isolde_decoder_busy_o <= 0;
    end else begin
      idvli_state <= idvli_next;
      case (idvli_next)
        BOOT: begin
          read_ptr <= read_ptr + 1;
        end
        IDLE: begin
          isolde_decoder_illegal_instr_o <= 0;
          isolde_decoder_rf_we_a_o <= 1'b0;
        end
        FETCH_COMPUTE: begin
          if (isolde_opcode_none == isolde_opcode_d) begin
            isolde_decoder_illegal_instr_o <= 1;
          end else begin
            read_ptr           <= 1;
            rd                 <= isolde_decoder_instr_batch_i[0][11:7];
            func7              <= isolde_decoder_instr_batch_i[0][31:25];
            isolde_opcode_q    <= isolde_opcode_d;
            vlen_instr_words_q <= vlen_instr_words_d;
          end
        end
        FETCH_REST: begin
          read_ptr <= read_ptr + 1;
          case (isolde_opcode_q)
            isolde_opcode_vle32_4: load_quad_word();
          endcase
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
        if (vlen_instr_words_q == read_ptr) begin
          isolde_decoder_busy_o = 0;
          idvli_next = IDLE;
        end
      end
    endcase
  end

  task static load_quad_word;
    begin
      if (3'h4 == read_ptr) begin
        isolde_decoder_rf_waddr_a_o <= rd;
        isolde_decoder_rf_wdata_a_o[3] <= isolde_decoder_instr_batch_i[0];
        isolde_decoder_rf_wdata_a_o[2] <= isolde_decoder_instr_batch_i[1];
        isolde_decoder_rf_wdata_a_o[1] <= isolde_decoder_instr_batch_i[2];
        isolde_decoder_rf_wdata_a_o[0] <= isolde_decoder_instr_batch_i[3];
        isolde_decoder_rf_we_a_o <= 1'b1;
      end
    end
  endtask
endmodule
