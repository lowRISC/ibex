// Copyright lowRISC contributors.
// Copyright 2017 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_tracer_defines;
import ibex_defines::*;

// instruction masks (for tracer)
parameter int unsigned INSTR_LUI     = { 25'b?,                           {OPCODE_LUI  } };
parameter int unsigned INSTR_AUIPC   = { 25'b?,                           {OPCODE_AUIPC} };
parameter int unsigned INSTR_JAL     = { 25'b?,                           {OPCODE_JAL  } };
parameter int unsigned INSTR_JALR    = { 17'b?,             3'b000, 5'b?, {OPCODE_JALR } };
// BRANCH
parameter int unsigned INSTR_BEQ     = { 17'b?,             3'b000, 5'b?, {OPCODE_BRANCH} };
parameter int unsigned INSTR_BNE     = { 17'b?,             3'b001, 5'b?, {OPCODE_BRANCH} };
parameter int unsigned INSTR_BLT     = { 17'b?,             3'b100, 5'b?, {OPCODE_BRANCH} };
parameter int unsigned INSTR_BGE     = { 17'b?,             3'b101, 5'b?, {OPCODE_BRANCH} };
parameter int unsigned INSTR_BLTU    = { 17'b?,             3'b110, 5'b?, {OPCODE_BRANCH} };
parameter int unsigned INSTR_BGEU    = { 17'b?,             3'b111, 5'b?, {OPCODE_BRANCH} };
parameter int unsigned INSTR_BALL    = { 17'b?,             3'b010, 5'b?, {OPCODE_BRANCH} };
// OPIMM
parameter int unsigned INSTR_ADDI    = { 17'b?,             3'b000, 5'b?, {OPCODE_OPIMM} };
parameter int unsigned INSTR_SLTI    = { 17'b?,             3'b010, 5'b?, {OPCODE_OPIMM} };
parameter int unsigned INSTR_SLTIU   = { 17'b?,             3'b011, 5'b?, {OPCODE_OPIMM} };
parameter int unsigned INSTR_XORI    = { 17'b?,             3'b100, 5'b?, {OPCODE_OPIMM} };
parameter int unsigned INSTR_ORI     = { 17'b?,             3'b110, 5'b?, {OPCODE_OPIMM} };
parameter int unsigned INSTR_ANDI    = { 17'b?,             3'b111, 5'b?, {OPCODE_OPIMM} };
parameter int unsigned INSTR_SLLI    = { 7'b0000000, 10'b?, 3'b001, 5'b?, {OPCODE_OPIMM} };
parameter int unsigned INSTR_SRLI    = { 7'b0000000, 10'b?, 3'b101, 5'b?, {OPCODE_OPIMM} };
parameter int unsigned INSTR_SRAI    = { 7'b0100000, 10'b?, 3'b101, 5'b?, {OPCODE_OPIMM} };
// OP
parameter int unsigned INSTR_ADD     = { 7'b0000000, 10'b?, 3'b000, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_SUB     = { 7'b0100000, 10'b?, 3'b000, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_SLL     = { 7'b0000000, 10'b?, 3'b001, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_SLT     = { 7'b0000000, 10'b?, 3'b010, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_SLTU    = { 7'b0000000, 10'b?, 3'b011, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_XOR     = { 7'b0000000, 10'b?, 3'b100, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_SRL     = { 7'b0000000, 10'b?, 3'b101, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_SRA     = { 7'b0100000, 10'b?, 3'b101, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_OR      = { 7'b0000000, 10'b?, 3'b110, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_AND     = { 7'b0000000, 10'b?, 3'b111, 5'b?, {OPCODE_OP} };

// SYSTEM
parameter int unsigned INSTR_CSRRW   = { 17'b?,             3'b001, 5'b?, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_CSRRS   = { 17'b?,             3'b010, 5'b?, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_CSRRC   = { 17'b?,             3'b011, 5'b?, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_CSRRWI  = { 17'b?,             3'b101, 5'b?, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_CSRRSI  = { 17'b?,             3'b110, 5'b?, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_CSRRCI  = { 17'b?,             3'b111, 5'b?, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_ECALL   = { 12'b000000000000,         13'b0, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_EBREAK  = { 12'b000000000001,         13'b0, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_MRET    = { 12'b001100000010,         13'b0, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_DRET    = { 12'b011110110010,         13'b0, {OPCODE_SYSTEM} };
parameter int unsigned INSTR_WFI     = { 12'b000100000101,         13'b0, {OPCODE_SYSTEM} };

// RV32M
parameter int unsigned INSTR_DIV     = { 7'b0000001, 10'b?, 3'b100, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_DIVU    = { 7'b0000001, 10'b?, 3'b101, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_REM     = { 7'b0000001, 10'b?, 3'b110, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_REMU    = { 7'b0000001, 10'b?, 3'b111, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_PMUL    = { 7'b0000001, 10'b?, 3'b000, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_PMUH    = { 7'b0000001, 10'b?, 3'b001, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_PMULHSU = { 7'b0000001, 10'b?, 3'b010, 5'b?, {OPCODE_OP} };
parameter int unsigned INSTR_PMULHU  = { 7'b0000001, 10'b?, 3'b011, 5'b?, {OPCODE_OP} };

endpackage
