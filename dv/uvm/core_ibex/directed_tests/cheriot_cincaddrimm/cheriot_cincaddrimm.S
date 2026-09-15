# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cincaddrimm — CIncAddrImm moves the cursor by an immediate
# =============================================================================
# CIncAddrImm (funct3=001, I-type) is the immediate-operand sibling of
# CIncAddr (funct7=0x11, R-type, already covered by cheriot_cinc_addr): it
# adds a 12-bit immediate to the capability's cursor instead of an integer
# register operand. ibex_decoder.sv: instr[14:12]==3'b001 under OPCODE_CHERI
# -> cheriot_operator_o.CINC_ADDR_IMM, adder_a=imm12, adder_b=rs1 (cursor).
#
# Tag semantics match CIncAddr: stays 1 when the new cursor is within
# [base, top), cleared otherwise. For MTCC (full range), any in-range
# increment keeps the tag set.
#
#   Test 1 (cursor moves from 0 to 4 after CIncAddrImm +4)
#   Test 2 (base unchanged after CIncAddrImm)
#   Test 3 (tag preserved after in-bounds CIncAddrImm)
#   Tests 4-6 (interrupt state — no interrupt expected)
#
# Verification: cosim (per-instruction Spike/RTL register compare) plus the
# self-check below (independent of cosim).
#
# CIncAddrImm encoding (imm=4, rs1=ca0=x10, rd=ca0=x10):
#   imm[11:0]=0000_0000_0100, rs1=01010, funct3=001, rd=01010, opcode=1011011
#   = 000000000100_01010_001_01010_1011011 = 0x0045155B
#
# Tests:
#   1. CGetAddr after CIncAddrImm(+4) = 4.
#   2. CGetBase unchanged = 0.
#   3. Tag = 1 (in-bounds increment).
#   4. mstatus.MIE = 1.
#   5. mcause = 0.
#   6. mip = 0.

.globl main
main:
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # Load MTCC (base=0, cursor=0, tag=1, full 32-bit range).
    .word   0x03C0055B              # cspecialr ca0, mtcc

    # Increment cursor by immediate 4.
    .word   0x0045155B              # cincaddrimm ca0, ca0, 4

    # ── Test 1: cursor is now 4 ───────────────────────────────────────────────
    .word   0xFEF5055B              # cgetaddr a0, ca0
    li      a2, 4
    bne     a0, a2, .Lfail_test1

    # ── Test 2: base unchanged = 0 ────────────────────────────────────────────
    .word   0xFE25055B              # cgetbase a0, ca0
    bne     a0, x0, .Lfail_test2

    # ── Test 3: tag = 1 (in-bounds, cursor=4 < top=2^32) ─────────────────────
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test3

    # ── Interrupt state verification ───────────────────────────────────────────
    csrr    a0, mstatus
    andi    a1, a0, 8
    beq     a1, x0, .Lfail_test4
    csrr    a0, mcause
    bne     a0, x0, .Lfail_test5
    csrr    a0, mip
    bne     a0, x0, .Lfail_test6

    li      a0, 0
    ret

.Lfail_test1: li a0, 1; ret
.Lfail_test2: li a0, 2; ret
.Lfail_test3: li a0, 3; ret
.Lfail_test4: li a0, 4; ret
.Lfail_test5: li a0, 5; ret
.Lfail_test6: li a0, 6; ret
