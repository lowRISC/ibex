////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineer:       Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Create Date:    10/06/2015                                                 //
// Design Name:    Compressed instruction decoder                             //
// Module Name:    compressed_decoder.sv                                      //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decodes RISC-V compressed instructions into their RV32     //
//                 equivalent. This module is fully combinatorial.            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "defines.sv"

module compressed_decoder
(
  input  logic [31:0] instr_i,
  output logic [31:0] instr_o,
  output logic        is_compressed_o,
  output logic        illegal_instr_o
);

  //////////////////////////////////////////////////////////////////////////////////////////////////////
  //   ____                                                 _   ____                     _            //
  //  / ___|___  _ __ ___  _ __  _ __ ___  ___ ___  ___  __| | |  _ \  ___  ___ ___   __| | ___ _ __  //
  // | |   / _ \| '_ ` _ \| '_ \| '__/ _ \/ __/ __|/ _ \/ _` | | | | |/ _ \/ __/ _ \ / _` |/ _ \ '__| //
  // | |__| (_) | | | | | | |_) | | |  __/\__ \__ \  __/ (_| | | |_| |  __/ (_| (_) | (_| |  __/ |    //
  //  \____\___/|_| |_| |_| .__/|_|  \___||___/___/\___|\__,_| |____/ \___|\___\___/ \__,_|\___|_|    //
  //                      |_|                                                                         //
  //////////////////////////////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    illegal_instr_o = 1'b0;
    is_compressed_o = 1'b1;
    instr_o         = '0;

    unique case (instr_i[1:0])
      // C0
      2'b00: begin
        unique case (instr_i[15:13])
          3'b000: begin
            if (instr_i[12] == 1'b0) begin
              // c.mv -> add rd, x0, rs2
              instr_o = {7'b0, instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], `OPCODE_OP};
            end else begin
              // c.add -> add rd, rd, rs2
              instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b000, instr_i[11:7], `OPCODE_OP};
            end
            if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
          end

          3'b001: begin
            // c.srai -> srai rd, rd, shamt
            instr_o = {2'b01, 5'b0, instr_i[6:2], instr_i[11:7], 3'b101, instr_i[11:7], `OPCODE_OPIMM};
            if (instr_i[12] != 1'b0)   illegal_instr_o = 1'b1;
            if (instr_i[6:2] == 5'b0)  illegal_instr_o = 1'b1;
            if (instr_i[11:7] == 5'b0) illegal_instr_o = 1'b1;
          end

          3'b010: begin
            // c.sw -> sw rs2', imm(rs1')
            instr_o = {5'b0, instr_i[5], instr_i[12], 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b010, instr_i[11:10], instr_i[6], 2'b00, `OPCODE_STORE};
          end

          3'b011: begin
            instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b0, 2'b01, instr_i[9:7], `OPCODE_OP};

            unique case ({instr_i[12:10], instr_i[6:5]})
              // c.xor -> xor rd', rd', rs2'
              5'b00000: instr_o = {7'b000_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b100, 2'b01, instr_i[9:7], `OPCODE_OP};

              // c.sll -> sll rd', rd', rs2'
              5'b00100: instr_o = {7'b000_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b001, 2'b01, instr_i[9:7], `OPCODE_OP};
              // c.srl -> srl rd', rd', rs2'
              5'b00101: instr_o = {7'b000_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b101, 2'b01, instr_i[9:7], `OPCODE_OP};
              // c.sra -> sra rd', rd', rs2'
              5'b00001: instr_o = {7'b010_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b101, 2'b01, instr_i[9:7], `OPCODE_OP};
              // c.sltu -> sltu rd', rd', rs2'
              5'b00111: instr_o = {7'b000_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b011, 2'b01, instr_i[9:7], `OPCODE_OP};

              // c.sllr -> sll rd', rs1', rd'
              5'b01100: instr_o = {7'b000_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b001, 2'b01, instr_i[4:2], `OPCODE_OP};
              // c.srlr -> srl rd', rs1', rd'
              5'b01101: instr_o = {7'b000_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b101, 2'b01, instr_i[4:2], `OPCODE_OP};
              // c.sltur -> sltu rd', rs1', rd'
              5'b01111: instr_o = {7'b000_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b011, 2'b01, instr_i[4:2], `OPCODE_OP};

              // c.slt -> slt rd', rd', rs2'
              5'b00110: instr_o = {7'b000_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b010, 2'b01, instr_i[9:7], `OPCODE_OP};
              // c.sltr -> slt rd', rs1', rd'
              5'b01110: instr_o = {7'b000_0000, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b010, 2'b01, instr_i[4:2], `OPCODE_OP};

              default:  illegal_instr_o = 1'b1;
            endcase
          end

          3'b100: begin
            // c.sub -> sub rd, rd rs2
            instr_o = {2'b01, 5'b0, instr_i[6:2], instr_i[11:7], 3'b000, instr_i[11:7], `OPCODE_OP};
            if (instr_i[12] != 1'b0)   illegal_instr_o = 1'b1;
            if (instr_i[6:2] == 5'b0)  illegal_instr_o = 1'b1;
            if (instr_i[11:7] == 5'b0) illegal_instr_o = 1'b1;
          end

          3'b101: begin
            unique case (instr_i[6:5])
              // c.add3 -> add rd', rs1', rs2'
              2'b00:  instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b000, 2'b01, instr_i[12:10], `OPCODE_OP};
              // c.sub3 -> sub rd', rs1', rs2'
              2'b01:  instr_o = {2'b01, 5'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b000, 2'b01, instr_i[12:10], `OPCODE_OP};
              // c.or3 -> or rd'1, rs1', rs2'
              2'b10:  instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b110, 2'b01, instr_i[12:10], `OPCODE_OP};
              // c.and3 -> and rd', rs1', rs2'
              2'b11:  instr_o = {7'b0, 2'b01, instr_i[4:2], 2'b01, instr_i[9:7], 3'b111, 2'b01, instr_i[12:10], `OPCODE_OP};
              default:  illegal_instr_o = 1'b1;
            endcase
          end

          3'b110: begin
            // c.lw -> lw rd', imm(rs1')
            instr_o = {5'b0, instr_i[5], instr_i[12:10], instr_i[6], 2'b00, 2'b01, instr_i[9:7], 3'b010, 2'b01, instr_i[4:2], `OPCODE_LOAD};
          end

          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
      end

      // C1
      2'b01: begin
        unique case (instr_i[15:13])
          3'b000: begin
            // c.slli -> slli rd, rd, shamt
            instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b001, instr_i[11:7], `OPCODE_OPIMM};
            if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
            if (instr_i[12] == 1'b1 || instr_i[6:2] == 5'b0)  illegal_instr_o = 1'b1;
          end

          3'b001: begin
            // c.srli -> srli rd, rd, shamt
            instr_o = {7'b0, instr_i[6:2], instr_i[11:7], 3'b101, instr_i[11:7], `OPCODE_OPIMM};
            if (instr_i[12] == 1'b1)   illegal_instr_o = 1'b1;
            if (instr_i[6:2] == 5'b0)  illegal_instr_o = 1'b1;
            if (instr_i[11:7] == 5'b0) illegal_instr_o = 1'b1;
          end

          3'b010: begin
            // c.swsp -> sw rs2, imm(x2)
            instr_o = {4'b0, instr_i[8:7], instr_i[12], instr_i[6:2], 5'h02, 3'b010, instr_i[11:9], 2'b00, `OPCODE_STORE};
          end

          3'b011: begin
            // c.bltz -> blt rs1', x0, imm
            instr_o = {{3 {instr_i[12]}}, instr_i[12:10], instr_i[2], 5'b0, 2'b01, instr_i[9:7], 3'b100, instr_i[6:3], instr_i[12], `OPCODE_BRANCH};
          end

          3'b100: begin
            unique case (instr_i[6:5])
              // c.addin -> addi rd', rs1', imm
              2'b00:  instr_o = {{9 {instr_i[12]}}, instr_i[12:10], 2'b01, instr_i[9:7], 3'b000, 2'b01, instr_i[4:2], `OPCODE_OPIMM};
              // c.xorin -> xori rd', rs1', imm
              2'b01:  instr_o = {{9 {instr_i[12]}}, instr_i[12:10], 2'b01, instr_i[9:7], 3'b100, 2'b01, instr_i[4:2], `OPCODE_OPIMM};
              // c.orin -> ori rd', rs1', imm
              2'b10:  instr_o = {{9 {instr_i[12]}}, instr_i[12:10], 2'b01, instr_i[9:7], 3'b110, 2'b01, instr_i[4:2], `OPCODE_OPIMM};
              // c.andin -> andi rd', rs1', imm
              2'b11:  instr_o = {{9 {instr_i[12]}}, instr_i[12:10], 2'b01, instr_i[9:7], 3'b111, 2'b01, instr_i[4:2], `OPCODE_OPIMM};
              default:  illegal_instr_o = 1'b1;
            endcase
            if (instr_i[12:10] == 3'b0) illegal_instr_o = 1'b1;
          end

          3'b101: begin
            // c.addi4spn -> addi rd', x2, imm
            instr_o = {2'b0, instr_i[10:7], instr_i[12:11], instr_i[5], instr_i[6], 2'b00, 5'h02, 3'b000, 2'b01, instr_i[4:2], `OPCODE_OPIMM};
          end

          3'b110: begin
            // c.lwsp -> lw rd, imm(x2)
            instr_o = {4'b0, instr_i[3:2], instr_i[12], instr_i[6:4], 2'b00, 5'h02, 3'b010, instr_i[11:7], `OPCODE_LOAD};
            if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
          end

          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
      end

      // C2
      2'b10: begin
        unique case (instr_i[15:13])
          3'b000, 3'b001: begin
            // 0: c.j -> jal x0, imm
            // 1: c.jal -> jal x1, imm
            instr_o = {instr_i[12], instr_i[11:7], instr_i[2], instr_i[6:3], {9 {instr_i[12]}}, 4'b0, instr_i[13], `OPCODE_JAL};
          end

          3'b010, 3'b011: begin
            // 0: c.beqz -> beq rs1', x0, imm
            // 1: c.bnez -> bne rs1', x0, imm
            instr_o = {{3 {instr_i[12]}}, instr_i[12:10], instr_i[2], 5'b0, 2'b01, instr_i[9:7], 2'b00, instr_i[13], instr_i[6:3], instr_i[12], `OPCODE_BRANCH};
          end

          3'b100: begin
            if ({instr_i[12], instr_i[6:2]} == 6'b0) begin
              // c.jr -> jalr x0, rs1, 0
              instr_o = {12'b0, instr_i[11:7], 3'b0, 5'b0, `OPCODE_JALR};
            end else begin
              // c.li -> addi rd, x0, nzimm
              instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], 5'b0, 3'b0, instr_i[11:7], `OPCODE_OPIMM};
            end
            if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
          end

          3'b101: begin
            if ({instr_i[12], instr_i[6:2]} == 6'b0) begin
              // c.jalr -> jalr x1, rs1, 0
              instr_o = {12'b0, instr_i[11:7], 3'b000, 5'b00001, `OPCODE_JALR};
            end else begin
              // c.lui -> lui rd, imm
              instr_o = {{15 {instr_i[12]}}, instr_i[6:2], instr_i[11:7], `OPCODE_LUI};
            end

            if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
          end

          3'b110: begin
            if (instr_i[11:7] == 5'b0) begin
              // c.addi16sp -> addi x2, x2, nzimm
              // c.nop
              instr_o = {{3 {instr_i[12]}}, instr_i[4:2], instr_i[5], instr_i[6], 4'b0, 5'h02, 3'b000, 5'h02, `OPCODE_OPIMM};
            end else begin
              // c.addi -> addi rd, rd, nzimm
              instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], instr_i[11:7], 3'b0, instr_i[11:7], `OPCODE_OPIMM};
              if ({instr_i[12], instr_i[6:2]} == 6'b0)  illegal_instr_o = 1'b1;
            end
          end

          3'b111: begin
            // c.andi -> andi rd, rd, nzimm
            instr_o = {{6 {instr_i[12]}}, instr_i[12], instr_i[6:2], instr_i[11:7], 3'b111, instr_i[11:7], `OPCODE_OPIMM};
            if (instr_i[11:7] == 5'b0)  illegal_instr_o = 1'b1;
          end

          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
      end

      2'b11: begin
        // 32 bit (or more) instruction
        instr_o = instr_i;
        is_compressed_o = 1'b0;
      end
    endcase
  end

endmodule
