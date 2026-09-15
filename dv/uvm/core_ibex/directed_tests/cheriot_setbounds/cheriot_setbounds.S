# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_setbounds — CSetBounds narrows a capability to a sub-region
# =============================================================================
# CSetBounds (funct7=0x08, R-type) derives a capability with:
#   new_base  = cs1.cursor  (current address)
#   new_top   = cs1.cursor + rs2  (rs2 = requested length)
#   new_tag   = 1 iff (cs1 was valid) AND (new_region ⊆ cs1 original bounds)
#
# The bounds use compressed (exponent-based) representation, so very small
# lengths are exact; larger ones are rounded up to the nearest representable
# value.  256 bytes (2^8) is exactly representable at exponent 0.
#
# CSetBoundsExact (funct7=0x09) would fail if rounding is needed; CSetBounds
# silently rounds up.  This test uses CSetBounds.
#
#   Test 1 (length after CSetBounds(MTDC, 256) = 256)
#     Start with MTDC (full range, length=0xFFFFFFFF).  After CSetBounds(256),
#     CGetLen should return exactly 256 (no rounding needed for power-of-two).
#     A failure means CSetBounds is not updating the bounds fields, or the
#     exponent calculation is wrong.
#
#   Test 2 (base after CSetBounds = 0)
#     The new base = cursor of MTDC at the time of CSetBounds = 0.
#     CGetBase should return 0.  A failure means the base derivation is wrong.
#
#   Test 3 (tag = 1 after in-range CSetBounds)
#     The new region [0, 256) is contained within the original MTDC bounds
#     [0, 2^32) → tag must remain 1.  A cleared tag means the bounds containment
#     check incorrectly rejected the derivation.
#
#   Test 4 (address (cursor) unchanged after CSetBounds)
#     CSetBounds sets base=cursor but does NOT change cursor.  CGetAddr must
#     still return 0.  A failure means CSetBounds is also moving the cursor,
#     which would break address-preserving derivation.
#
#   Tests 5-7 (interrupt state — no interrupt expected)
#     Machine-mode interrupts are enabled at the start of the test.
#     Test 5: mstatus.MIE still = 1.
#     Test 6: mcause = 0.
#     Test 7: mip = 0.
#
# Verification:
#   Two independent layers catch a faulty DUT:
#
#   1. Cosim (Spike vs ibex RTL, per instruction step):
#      cgetlen, cgetbase, cgettag, and cgetaddr all write to integer register
#      a0 → cosim verifies each result.  Wrong bounds after CSetBounds diverge
#      Spike from the DUT immediately.
#
#   2. Self-check (bne/beq against expected constants):
#      main() returns non-zero if any check fails → UVM testbench marks FAILED.
#
# Inspired by clang_purecap_array.c (array capability bounds) and
# clang_purecap_stack_cap.c (stack capability bounds) from CTSRD/Cambridge.
# CSetBounds is the fundamental instruction for enforcing spatial safety.
# =============================================================================
#
# CSetBounds encoding (funct7=0x08, rs1=ca0=x10, rs2=a1=x11, rd=ca0=x10):
#   funct7=0b0001000, rs2=0b01011, rs1=0b01010, funct3=000, rd=0b01010
#   = 0001000_01011_01010_000_01010_1011011 = 0x10B5055B
#
# Tests:
#   1. CGetLen after CSetBounds(MTDC, 256) = 256.
#   2. CGetBase after CSetBounds = 0 (new base = cursor = 0).
#   3. Tag = 1 (sub-region is inside original full-range bounds).
#   4. CGetAddr after CSetBounds = 0 (cursor unchanged).
#   5. mstatus.MIE = 1.
#   6. mcause = 0.
#   7. mip = 0.

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # Load MTDC (full range, base=0, cursor=0, length=0xFFFFFFFF, tag=1).
    .word   0x03D0055B              # cspecialr ca0, mtdc

    # Narrow to 256 bytes (base=cursor=0, length=256).
    li      a1, 256
    .word   0x10B5055B              # csetbounds ca0, ca0, a1

    # ── Test 1: length = 256 after CSetBounds ─────────────────────────────────
    .word   0xFE35055B              # cgetlen a0, ca0
    li      a2, 256
    bne     a0, a2, .Lfail_test1

    # ── Test 2: base = 0 (cursor was 0 when CSetBounds was applied) ───────────
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
