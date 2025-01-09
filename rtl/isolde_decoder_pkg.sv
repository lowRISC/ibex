// Copyleft 2024

package isolde_decoder_pkg;

  typedef enum logic [5:0] {
    isolde_opcode_invalid,
    isolde_opcode_nop,
    isolde_opcode_vle32_4,
    isolde_opcode_gemm,
    isolde_opcode_conv2d,
    isolde_opcode_R_type,
    isolde_opcode_redmule,
    isolde_opcode_redmule_gemm
  } isolde_opcode_e;


  task static decode_isolde_opcode(
      input logic [6:0] opCode_i, input logic [2:0] nnn_i, input logic [6:0] func7_i,
      output isolde_opcode_e isolde_op_code_o, output logic [2:0] vlen_instr_words_o);
    // Define constants for custom encodings
    localparam logic [6:0] RISCV_ENC_GE80 = 7'b1111111;  // Custom opcode for GE80 (160-bit or 96-bit instructions)
    localparam logic [6:0] RISCV_ENC_64   = 7'b0111111;  // Custom opcode for 64-bit instruction (2 words)
    localparam logic [6:0] RISCV_ENC_C0   = 7'b0001011;  // Custom-0 opcode for 32-bit instruction (1 word) 
    localparam logic [6:0] RISCV_ENC_C1   = 7'b0101011;  // Custom-1 opcode for 32-bit instruction (1 word) 
    localparam logic [6:0] RISCV_ENC_C2   = 7'b1011011;  // Custom-2 opcode for 32-bit instruction (1 word) 
    localparam logic [6:0] RISCV_ENC_C3   = 7'b1111011;  // Custom-3 opcode for 32-bit instruction (1 word) 

    localparam logic [2:0] RISCV_ENC_GE80_N5 = 3'h5;  // Custom encoding for N5 (5 words)
    localparam logic [2:0] RISCV_ENC_GE80_N3 = 3'h3;  // Custom encoding for N5 (5 words)
    localparam logic [2:0] RISCV_ENC_GE80_N1 = 3'h1;  // Custom encoding for N1 (3 words)
    begin
      case (opCode_i)
        RISCV_ENC_GE80: begin
          if (nnn_i == RISCV_ENC_GE80_N5) begin
            vlen_instr_words_o = 5;
            case (func7_i)
              7'b0000011: isolde_op_code_o = isolde_opcode_vle32_4;
              default: isolde_op_code_o = isolde_opcode_nop;
            endcase
          end else if (nnn_i == RISCV_ENC_GE80_N3) begin
            vlen_instr_words_o = 4;
            case (func7_i)
              7'b0000100: isolde_op_code_o = isolde_opcode_redmule_gemm;
              default: isolde_op_code_o = isolde_opcode_nop;
            endcase
          end else if (nnn_i == RISCV_ENC_GE80_N1) begin
            vlen_instr_words_o = 3;
            case (func7_i)
              7'b0000000: isolde_op_code_o = isolde_opcode_conv2d;
              default: isolde_op_code_o = isolde_opcode_nop;
            endcase
          end else isolde_op_code_o = isolde_opcode_invalid;
        end
        RISCV_ENC_64: begin
          vlen_instr_words_o = 2;
          case (func7_i)
            7'b0000111: isolde_op_code_o = isolde_opcode_gemm;
            default: isolde_op_code_o = isolde_opcode_nop;
          endcase
        end
        RISCV_ENC_C0: begin
          vlen_instr_words_o = 1;
          isolde_op_code_o = isolde_opcode_R_type;
        end
        RISCV_ENC_C1: begin
          vlen_instr_words_o = 1;
          isolde_op_code_o = isolde_opcode_redmule;
        end
        default: isolde_op_code_o = isolde_opcode_invalid;
      endcase
    end
  endtask

endpackage
