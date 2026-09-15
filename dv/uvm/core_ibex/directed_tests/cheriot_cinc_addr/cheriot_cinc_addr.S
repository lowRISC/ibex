# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cinc_addr — CIncAddr moves the capability cursor in-bounds
# =============================================================================
# CIncAddr (funct7=0x11, R-type with rs1=capability, rs2=integer offset) adds
# an integer offset to the cursor of a capability.  The result's tag remains 1
# Tag stays 1 when the new cursor is within [base, top); cleared otherwise.
#
# ibex_decoder.sv: 7'h11 → CINC_ADDR, cheri_adder_a_sel = CHERI_ADDER_A_RS2
#
# For MTCC (full range 0x00000000–0xFFFFFFFF, base=0, top=2^32):
#   Any increment that keeps cursor within 32-bit space is within bounds.
#   Specifically: +4 → cursor=4, which is inside [0, 2^32) → tag stays 1.
#
#   Test 1 (cursor moves from 0 to 4 after CIncAddr +4)
#     Verifies that CIncAddr correctly updates the cursor.  CGetAddr should
#     return 4.  A failure means CIncAddr is either not decoded or the adder
#     result is not written back to the address shadow register.
#
#   Test 2 (base unchanged after CIncAddr)
#     CIncAddr must NOT change the base address.  CGetBase should still
#     return 0.  A failure means the bounds fields are being incorrectly
#     modified by the address increment.
#
#   Test 3 (tag preserved after in-bounds CIncAddr)
#     Since cursor=4 is within MTCC's full range, the capability remains
#     valid.  A cleared tag here means the bounds check is incorrectly
#     triggering an out-of-bounds violation.
#
#   Tests 4-6 (interrupt state — no interrupt expected)
#     Machine-mode interrupts are enabled at the start of the test.
#     Test 4: mstatus.MIE still = 1.
#     Test 5: mcause = 0.
#     Test 6: mip = 0.
#
# Verification:
#   Two independent layers catch a faulty DUT:
#
#   1. Cosim (Spike vs ibex RTL, per instruction step):
#      cgetaddr, cgetbase, and cgettag all write to integer register a0 →
#      cosim verifies each result.  A wrong cursor increment or unexpected
#      tag-clear immediately diverges Spike from the DUT.
#
#   2. Self-check (bne against expected constants):
#      main() returns non-zero if any check fails → UVM testbench marks FAILED.
#
# Inspired by clang_purecap_capcmp.c pointer arithmetic and
# clang_purecap_intcap.c foo += offset operations (CTSRD/Cambridge).
# =============================================================================
#
# CIncAddr encoding (funct7=0x11, rs1=ca0=x10, rs2=a1=x11, rd=ca0=x10):
#   funct7=0b0010001, rs2=0b01011, rs1=0b01010, funct3=000, rd=0b01010
#   = 0010001_01011_01010_000_01010_1011011 = 0x22B5055B
#
# Tests:
#   1. CGetAddr after CIncAddr(+4) = 4.
#   2. CGetBase unchanged = 0.
#   3. Tag = 1 (in-bounds increment).
#   4. mstatus.MIE = 1.
#   5. mcause = 0.
#   6. mip = 0.

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # Load MTCC (base=0, cursor=0, tag=1, full 32-bit range).
    .word   0x03C0055B              # cspecialr ca0, mtcc

    # Increment cursor by 4.
    li      a1, 4
    .word   0x22B5055B              # cincaddr ca0, ca0, a1

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
