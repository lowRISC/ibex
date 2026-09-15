# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_setboundsexact — CSetBoundsExact rejects non-exact rounding
# =============================================================================
# CSetBoundsExact (funct7=0x09, R-type) behaves like CSetBounds but with
# req_exact=1 passed to cheriot_set_bounds_ex() (ibex_cheriot_pkg.sv): if the
# requested [cursor, cursor+len) region needed ANY rounding to fit the
# compressed representation (topoff | baseoff != 0), the result's tag is
# cleared instead of silently rounding up. ibex_decoder.sv: funct7=0x09 ->
# cheriot_operator_o.CSET_BOUNDS_EX, cheriot_setbounds_sel=SETBOUNDS_RS2_EX.
#
# Two vectors, both starting from MTDC (base=0, cursor=0, full range):
#   - len=256 (2^8): exactly representable at exponent 0 -> no rounding
#     needed -> tag stays 1 (same vector cheriot_setbounds already uses to
#     confirm the non-exact CSetBounds path succeeds here too).
#   - len=300: not a power of two, needs rounding to fit the compressed
#     mantissa -> topoff/baseoff fire -> tag must be CLEARED (0), unlike
#     plain CSetBounds which would silently round up and keep tag=1.
#
#   Test 1 (CSetBoundsExact(MTDC,256): tag=1, no rounding needed)
#   Test 2 (CGetLen after exact case = 256)
#   Test 3 (CSetBoundsExact(MTDC,300): tag=0, rounding was required)
#   Tests 4-6 (interrupt state — no interrupt expected)
#
# Verification: cosim (per-instruction Spike/RTL register compare) plus the
# self-check below (independent of cosim).
#
# CSetBoundsExact encoding (cs1=ca0=x10, rs2=a1=x11, rd=ca0=x10):
#   funct7=0b0001001, rs2=0b01011, rs1=0b01010, funct3=000, rd=0b01010
#   = 0001001_01011_01010_000_01010_1011011 = 0x12B5055B
#
# Tests:
#   1. Tag = 1 after CSetBoundsExact(MTDC, 256) (exactly representable).
#   2. CGetLen after that = 256.
#   3. Tag = 0 after CSetBoundsExact(MTDC, 300) (not exactly representable).
#   4. mstatus.MIE = 1.
#   5. mcause = 0.
#   6. mip = 0.

.globl main
main:
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # ── Vector 1: len=256, exactly representable ──────────────────────────────
    .word   0x03D0055B              # cspecialr ca0, mtdc
    li      a1, 256
    .word   0x12B5055B              # csetboundsexact ca0, ca0, a1

    # ── Test 1: tag = 1 (no rounding needed) ──────────────────────────────────
    .word   0xFE45055B              # cgettag a0, ca0
    li      a2, 1
    bne     a0, a2, .Lfail_test1

    # ── Test 2: length = 256 ───────────────────────────────────────────────────
    .word   0xFE35055B              # cgetlen a0, ca0
    li      a2, 256
    bne     a0, a2, .Lfail_test2

    # ── Vector 2: len=300, NOT exactly representable ─────────────────────────
    .word   0x03D0055B              # cspecialr ca0, mtdc
    li      a1, 300
    .word   0x12B5055B              # csetboundsexact ca0, ca0, a1

    # ── Test 3: tag = 0 (rounding was required, req_exact rejects it) ────────
    .word   0xFE45055B              # cgettag a0, ca0
    bnez    a0, .Lfail_test3

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
