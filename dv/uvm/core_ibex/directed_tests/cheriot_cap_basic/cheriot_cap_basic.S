# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# CHERIoT mode from reset: a 16-byte capability derived from mtdc, its fields, and memory
# accesses through it. CHERIoT instructions use .insn, which the toolchain encodes as given.

#include "ibex_macros.h"

# OPCODE_CHERI: funct7 0x7f reads the field rs2 selects; funct7 0x01 is CSpecialRW (rs2 = SCR)
.macro cspecialr_mtdc cd
  .insn r 0x5b, 0, 0x01, \cd, x0, x29
.endm
.macro cgetbase rd, cs1
  .insn r 0x5b, 0, 0x7f, \rd, \cs1, x2
.endm
.macro cgetlen rd, cs1
  .insn r 0x5b, 0, 0x7f, \rd, \cs1, x3
.endm
.macro cgettag rd, cs1
  .insn r 0x5b, 0, 0x7f, \rd, \cs1, x4
.endm
.macro ccleartag cd, cs1
  .insn r 0x5b, 0, 0x7f, \cd, \cs1, x11
.endm
.macro cgetaddr rd, cs1
  .insn r 0x5b, 0, 0x7f, \rd, \cs1, x15
.endm
.macro csetaddr cd, cs1, rs2
  .insn r 0x5b, 0, 0x10, \cd, \cs1, \rs2
.endm
.macro cincaddrimm cd, cs1, imm
  .insn i 0x5b, 1, \cd, \cs1, \imm
.endm
.macro csetboundsimm cd, cs1, imm
  .insn i 0x5b, 2, \cd, \cs1, \imm
.endm

  .section .text.init
  .globl _start

# Traps go to the boot address (mtcc keeps mtvec's reset value); no trap is expected.
trap_handler:
  j fail

  .org 0x80
_start:
  # The root memory capability (reset value of mtdc) is tagged
  cspecialr_mtdc x5
  cgettag x6, x5
  li x7, 1
  bne x6, x7, fail

  # Moving its address to the buffer keeps the tag
  lui x8, %hi(buffer)
  addi x8, x8, %lo(buffer)
  csetaddr x5, x5, x8
  cgetaddr x6, x5
  bne x6, x8, fail
  cgettag x6, x5
  bne x6, x7, fail

  # Bounds of 16 bytes are exact: base is the buffer, length 16, still tagged
  csetboundsimm x5, x5, 16
  cgetbase x6, x5
  bne x6, x8, fail
  cgetlen x6, x5
  li x9, 16
  bne x6, x9, fail
  cgettag x6, x5
  bne x6, x7, fail

  # Stores and loads through the bounded capability, at its base and 4 bytes above
  li x10, 0x5a5a1234
  sw x10, 0(x5)
  cincaddrimm x11, x5, 4
  cgetaddr x6, x11
  addi x12, x8, 4
  bne x6, x12, fail
  not x13, x10
  sw x13, 0(x11)
  lw x6, 0(x5)
  bne x6, x10, fail
  lw x6, 0(x11)
  bne x6, x13, fail

  # CClearTag clears only the tag
  ccleartag x14, x5
  cgettag x6, x14
  bne x6, x0, fail
  cgetaddr x6, x14
  bne x6, x8, fail

pass:
  li x15, (TEST_PASS << 8) | TEST_RESULT
  j finish
fail:
  li x15, (TEST_FAIL << 8) | TEST_RESULT
finish:
  # Stores need a capability, so the signature is written through one derived from mtdc
  cspecialr_mtdc x2
  li x3, SIGNATURE_ADDR
  csetaddr x2, x2, x3
  li x1, (FINISHED_IRQ << 8) | CORE_STATUS
  sw x1, 0(x2)
  sw x15, 0(x2)
1:
  j 1b

  .data
  .align 4
buffer:
  .word 0, 0, 0, 0
