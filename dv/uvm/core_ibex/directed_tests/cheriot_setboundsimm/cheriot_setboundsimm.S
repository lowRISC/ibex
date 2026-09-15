# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_setboundsimm — CSetBoundsImm narrows bounds by an immediate
# =============================================================================
# CSetBoundsImm (funct3=010, I-type) is the immediate-operand sibling of
# CSetBounds (funct7=0x08, R-type, already covered by cheriot_setbounds): the
# requested length comes from a 12-bit immediate (unsigned) instead of an
# integer register. ibex_decoder.sv: instr[14:12]==3'b010 under OPCODE_CHERI
# -> cheriot_operator_o.CSET_BOUNDS_IMM, cheriot_setbounds_sel=SETBOUNDS_IMM
# (ibex_cheriot_ex.sv: newlen=imm12, same cheriot_set_bounds_ex() datapath as
# plain CSetBounds, so identical rounding/tag rules apply).
#
# 256 bytes (2^8) is exactly representable at exponent 0, same reasoning as
# cheriot_setbounds's test vector.
#
#   Test 1 (length after CSetBoundsImm(MTDC, 256) = 256)
#   Test 2 (base after CSetBoundsImm = 0)
#   Test 3 (tag = 1 after in-range CSetBoundsImm)
#   Test 4 (address (cursor) unchanged after CSetBoundsImm)
#   Tests 5-7 (interrupt state — no interrupt expected)
#
# Verification: cosim (per-instruction Spike/RTL register compare) plus the
# self-check below (independent of cosim).
#
# CSetBoundsImm encoding (imm=256, cs1=ca0=x10, rd=ca0=x10):
#   imm[11:0]=0001_0000_0000, rs1=01010, funct3=010, rd=01010, opcode=1011011
#   = 000100000000_01010_010_01010_1011011 = 0x1005255B
#
# Tests:
#   1. CGetLen after CSetBoundsImm(MTDC,256) = 256.
#   2. CGetBase after CSetBoundsImm = 0.
#   3. Tag = 1 (sub-region is inside original full-range bounds).
#   4. CGetAddr after CSetBoundsImm = 0 (cursor unchanged).
#   5. mstatus.MIE = 1.
#   6. mcause = 0.
#   7. mip = 0.

.globl main
main:
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # Load MTDC (full range, base=0, cursor=0, length=0xFFFFFFFF, tag=1).
    .word   0x03D0055B              # cspecialr ca0, mtdc

    # Narrow to 256 bytes via immediate (base=cursor=0, length=256).
    .word   0x1005255B              # csetboundsimm ca0, ca0, 256

    # ── Test 1: length = 256 after CSetBoundsImm ──────────────────────────────
    .word   0xFE35055B              # cgetlen a0, ca0
    li      a2, 256
    bne     a0, a2, .Lfail_test1

    # ── Test 2: base = 0 (cursor was 0 when CSetBoundsImm was applied) ───────
    .word   0xFE25055B              # cgetbase a0, ca0
    bne     a0, x0, .Lfail_test2

    # ── Test 3: tag = 1 ([0,256) ⊆ [0,2^32) → derivation is legal) ───────────
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test3

    # ── Test 4: cursor unchanged = 0 ──────────────────────────────────────────
    .word   0xFEF5055B              # cgetaddr a0, ca0
    bne     a0, x0, .Lfail_test4

    # ── Interrupt state verification ───────────────────────────────────────────
    csrr    a0, mstatus
    andi    a1, a0, 8
    beq     a1, x0, .Lfail_test5
    csrr    a0, mcause
    bne     a0, x0, .Lfail_test6
    csrr    a0, mip
    bne     a0, x0, .Lfail_test7

    li      a0, 0
    ret

.Lfail_test1: li a0, 1; ret
.Lfail_test2: li a0, 2; ret
.Lfail_test3: li a0, 3; ret
.Lfail_test4: li a0, 4; ret
.Lfail_test5: li a0, 5; ret
.Lfail_test6: li a0, 6; ret
.Lfail_test7: li a0, 7; ret
