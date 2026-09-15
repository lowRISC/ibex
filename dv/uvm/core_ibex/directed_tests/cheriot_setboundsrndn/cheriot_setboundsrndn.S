# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_setboundsrndn — CSetBoundsRoundDown rounds length DOWN
# =============================================================================
# CSetBoundsRoundDown (funct7=0x0a, R-type) derives bounds via a SEPARATE
# datapath from plain CSetBounds: cheriot_set_bounds_rounddown()
# (ibex_cheriot_pkg.sv), rather than cheriot_set_bounds_ex(). Where plain
# CSetBounds rounds the requested length UP to the next representable value
# (so the derived region always contains the request), RoundDown rounds DOWN
# (so the derived region is always contained WITHIN the request) -- useful
# for callers that must never grant more than asked. ibex_decoder.sv:
# funct7=0x0a -> cheriot_operator_o.CSET_BOUNDS_RNDN,
# cheriot_setbounds_sel=SETBOUNDS_RNDN.
#
# len=300 is not a power of two, so it is NOT exactly representable at any
# single exponent -- this is the same property cheriot_setboundsexact relies
# on to prove rounding occurred. Here it proves CSetBounds and
# CSetBoundsRoundDown genuinely diverge: from the same MTDC (base=0, cursor=0,
# full range) and the same requested length, plain CSetBounds must round UP
# (result length >= 300) while CSetBoundsRoundDown must round DOWN (result
# length <= 300); if 300 required rounding at all (which it does), the two
# results are strictly different lengths.
#
#   Test 1 (CGetLen after CSetBoundsRoundDown(MTDC,300) <= 300)
#   Test 2 (CGetBase after CSetBoundsRoundDown = 0, cursor was 0)
#   Test 3 (tag = 1: rounding down from a full-range cap always stays in-bounds)
#   Test 4 (round-down length is strictly less than plain CSetBounds's
#           round-up length for the same request -- proves the two
#           instructions take genuinely different datapaths, not just an
#           alias of each other)
#   Tests 5-7 (interrupt state — no interrupt expected)
#
# Verification: cosim (per-instruction Spike/RTL register compare) plus the
# self-check below (independent of cosim).
#
# CSetBoundsRoundDown encoding (cs1=ca0=x10, rs2=a1=x11, rd=ca0=x10):
#   funct7=0b0001010, rs2=0b01011, rs1=0b01010, funct3=000, rd=0b01010
#   = 0001010_01011_01010_000_01010_1011011 = 0x14B5055B
# CSetBounds encoding (plain, round-up; already verified by cheriot_setbounds):
#   0x10B5055B

.globl main
main:
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # ── CSetBoundsRoundDown(MTDC, 300) ────────────────────────────────────────
    .word   0x03D0055B              # cspecialr ca0, mtdc
    li      a1, 300
    .word   0x14B5055B              # csetboundsrndn ca0, ca0, a1

    # ── Test 1: length <= 300 (rounded DOWN, never exceeds request) ──────────
    .word   0xFE35055B              # cgetlen a0, ca0
    mv      t0, a0                  # t0 = round-down length, kept for Test 4
    li      a2, 301
    bgeu    a0, a2, .Lfail_test1    # fail if length >= 301 (i.e. length > 300)

    # ── Test 2: base = 0 (cursor was 0) ───────────────────────────────────────
    .word   0xFE25055B              # cgetbase a0, ca0
    bne     a0, x0, .Lfail_test2

    # ── Test 3: tag = 1 (subset of full-range MTDC is always in-bounds) ──────
    .word   0xFE45055B              # cgettag a0, ca0
    li      a2, 1
    bne     a0, a2, .Lfail_test3

    # ── Plain CSetBounds(MTDC, 300) for comparison (rounds UP) ────────────────
    .word   0x03D0055B              # cspecialr ca0, mtdc
    li      a1, 300
    .word   0x10B5055B              # csetbounds ca0, ca0, a1
    .word   0xFE35055B              # cgetlen a0, ca0   -> round-up length

    # ── Test 4: round-down length (t0) strictly less than round-up length ────
    bgeu    t0, a0, .Lfail_test4

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
