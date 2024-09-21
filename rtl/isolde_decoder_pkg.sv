// Copyleft 2024

package isolde_decoder_pkg;

typedef enum logic [5:0] {
  isolde_opcode_none,
  isolde_opcode_vle32_4
} isolde_opcode_e;


task static decode_isolde_opcode(input logic [6:0] opCode_i, input logic [2:0] nnn_i,
                                 input logic [6:0] func7_i, output isolde_opcode_e isolde_op_code_o,
                                 output logic [2:0] vlen_instr_words_o);
  // Define constants for custom encodings
  localparam logic [6:0] RISCV_ENC_GE80 = 7'b1111111;  // Custom opcode for GE80 (160-bit or 96-bit instructions)
  localparam logic [6:0] RISCV_ENC_64   = 7'b0111111;  // Custom opcode for 64-bit instruction (2 words)

  localparam logic [2:0] RISCV_ENC_GE80_N5 = 3'h5;  // Custom encoding for N5 (5 words)
  localparam logic [2:0] RISCV_ENC_GE80_N1 = 3'h1;  // Custom encoding for N1 (3 words)
  begin
    case (opCode_i)
      RISCV_ENC_GE80: begin
        if (nnn_i == RISCV_ENC_GE80_N5) begin
          vlen_instr_words_o = 5;
          case (func7_i)
            7'b0000011: isolde_op_code_o = isolde_opcode_vle32_4;
            default: isolde_op_code_o = isolde_opcode_none;
          endcase
        end else if (nnn_i == RISCV_ENC_GE80_N1) begin
          vlen_instr_words_o = 3;
          case (func7_i)
            default: isolde_op_code_o = isolde_opcode_none;
          endcase
        end else isolde_op_code_o = isolde_opcode_none;
      end
      RISCV_ENC_64: begin
        vlen_instr_words_o = 2;
        case (func7_i)
          default: isolde_op_code_o = isolde_opcode_none;
        endcase
      end
      default: isolde_op_code_o = isolde_opcode_none;
    endcase
  end
endtask

endpackage