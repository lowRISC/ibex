// Copyright 2017 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

package zeroriscy_tracer_defines;
import zeroriscy_defines::*;

// instruction masks (for tracer)
// parameter INSTR_CUSTOM0   = { 25'b?, OPCODE_CUST0 };
// parameter INSTR_CUSTOM1   = { 25'b?, OPCODE_CUST1 };
parameter INSTR_LUI       = { 25'b?, OPCODE_LUI };
parameter INSTR_AUIPC     = { 25'b?, OPCODE_AUIPC };
parameter INSTR_JAL       = { 25'b?, OPCODE_JAL };
parameter INSTR_JALR      = { 17'b?, 3'b000, 5'b?, OPCODE_JALR };
// BRANCH
parameter INSTR_BEQ      =  { 17'b?, 3'b000, 5'b?, OPCODE_BRANCH };
parameter INSTR_BNE      =  { 17'b?, 3'b001, 5'b?, OPCODE_BRANCH };
parameter INSTR_BLT      =  { 17'b?, 3'b100, 5'b?, OPCODE_BRANCH };
parameter INSTR_BGE      =  { 17'b?, 3'b101, 5'b?, OPCODE_BRANCH };
parameter INSTR_BLTU     =  { 17'b?, 3'b110, 5'b?, OPCODE_BRANCH };
parameter INSTR_BGEU     =  { 17'b?, 3'b111, 5'b?, OPCODE_BRANCH };
parameter INSTR_BALL     =  { 17'b?, 3'b010, 5'b?, OPCODE_BRANCH };
// OPIMM
parameter INSTR_ADDI     =  { 17'b?, 3'b000, 5'b?, OPCODE_OPIMM };
parameter INSTR_SLTI     =  { 17'b?, 3'b010, 5'b?, OPCODE_OPIMM };
parameter INSTR_SLTIU    =  { 17'b?, 3'b011, 5'b?, OPCODE_OPIMM };
parameter INSTR_XORI     =  { 17'b?, 3'b100, 5'b?, OPCODE_OPIMM };
parameter INSTR_ORI      =  { 17'b?, 3'b110, 5'b?, OPCODE_OPIMM };
parameter INSTR_ANDI     =  { 17'b?, 3'b111, 5'b?, OPCODE_OPIMM };
parameter INSTR_SLLI     =  { 7'b0000000, 10'b?, 3'b001, 5'b?, OPCODE_OPIMM };
parameter INSTR_SRLI     =  { 7'b0000000, 10'b?, 3'b101, 5'b?, OPCODE_OPIMM };
parameter INSTR_SRAI     =  { 7'b0100000, 10'b?, 3'b101, 5'b?, OPCODE_OPIMM };
// OP
parameter INSTR_ADD      =  { 7'b0000000, 10'b?, 3'b000, 5'b?, OPCODE_OP };
parameter INSTR_SUB      =  { 7'b0100000, 10'b?, 3'b000, 5'b?, OPCODE_OP };
parameter INSTR_SLL      =  { 7'b0000000, 10'b?, 3'b001, 5'b?, OPCODE_OP };
parameter INSTR_SLT      =  { 7'b0000000, 10'b?, 3'b010, 5'b?, OPCODE_OP };
parameter INSTR_SLTU     =  { 7'b0000000, 10'b?, 3'b011, 5'b?, OPCODE_OP };
parameter INSTR_XOR      =  { 7'b0000000, 10'b?, 3'b100, 5'b?, OPCODE_OP };
parameter INSTR_SRL      =  { 7'b0000000, 10'b?, 3'b101, 5'b?, OPCODE_OP };
parameter INSTR_SRA      =  { 7'b0100000, 10'b?, 3'b101, 5'b?, OPCODE_OP };
parameter INSTR_OR       =  { 7'b0000000, 10'b?, 3'b110, 5'b?, OPCODE_OP };
parameter INSTR_AND      =  { 7'b0000000, 10'b?, 3'b111, 5'b?, OPCODE_OP };

// SYSTEM
parameter INSTR_CSRRW    =  { 17'b?, 3'b001, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRS    =  { 17'b?, 3'b010, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRC    =  { 17'b?, 3'b011, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRWI   =  { 17'b?, 3'b101, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRSI   =  { 17'b?, 3'b110, 5'b?, OPCODE_SYSTEM };
parameter INSTR_CSRRCI   =  { 17'b?, 3'b111, 5'b?, OPCODE_SYSTEM };
parameter INSTR_ECALL    =  { 12'b000000000000, 13'b0, OPCODE_SYSTEM };
parameter INSTR_EBREAK   =  { 12'b000000000001, 13'b0, OPCODE_SYSTEM };
parameter INSTR_MRET     =  { 12'b001100000010, 13'b0, OPCODE_SYSTEM };
parameter INSTR_WFI      =  { 12'b000100000101, 13'b0, OPCODE_SYSTEM };

// RV32M
parameter INSTR_DIV      =  { 7'b0000001, 10'b?, 3'b100, 5'b?, OPCODE_OP };
parameter INSTR_DIVU     =  { 7'b0000001, 10'b?, 3'b101, 5'b?, OPCODE_OP };
parameter INSTR_REM      =  { 7'b0000001, 10'b?, 3'b110, 5'b?, OPCODE_OP };
parameter INSTR_REMU     =  { 7'b0000001, 10'b?, 3'b111, 5'b?, OPCODE_OP };
parameter INSTR_PMUL     =  { 7'b0000001, 10'b?, 3'b000, 5'b?, OPCODE_OP };
parameter INSTR_PMUH     =  { 7'b0000001, 10'b?, 3'b001, 5'b?, OPCODE_OP };
parameter INSTR_PMULHSU  =  { 7'b0000001, 10'b?, 3'b010, 5'b?, OPCODE_OP };
parameter INSTR_PMULHU   =  { 7'b0000001, 10'b?, 3'b011, 5'b?, OPCODE_OP };


endpackage