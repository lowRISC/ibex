# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_csetaddr — CSetAddr moves the capability cursor to a new address
# =============================================================================
# CSetAddr (funct7=0x10, R-type) sets the cursor of a capability to an absolute
# address from an integer register, replacing the current cursor.  Unlike
# CIncAddr (funct7=0x11) which adds a relative offset, CSetAddr is an absolute
# placement.  The tag is preserved iff the new address is within [base, top).
#
# ibex_decoder.sv: 7'h10 → CSET_ADDR, cheri_adder_a_sel = CHERI_ADDER_A_RS2
#
# For MTCC (full range, base=0, top=2^32):
#   Any 32-bit address is within bounds → tag=1 after CSetAddr.
#
#   Test 1 (cursor set to 0x1000)
#     After CSetAddr(0x1000), CGetAddr must return 0x1000.  A failure means
#     CSetAddr is not writing the address back, or is writing the wrong value.
#
#   Test 2 (base unchanged after CSetAddr)
#     CSetAddr only changes the cursor, not the base.  CGetBase must still
#     return 0.  A failure indicates that the base field is being corrupted.
#
#   Test 3 (tag preserved after in-bounds CSetAddr)
#     0x1000 is within MTCC's full range → tag stays 1.
#
#   Test 4 (CGetAddr after a second CSetAddr = 0)
#     Set the cursor back to 0 to verify CSetAddr is not stuck (i.e., that
#     the address can be set to different values in sequence).
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
#      cgetaddr, cgetbase, and cgettag all write to integer register a0 →
#      cosim verifies each result.
#
#   2. Self-check (bne against expected constants):
#      main() returns non-zero if any check fails → UVM testbench marks FAILED.
#
# Inspired by clang_purecap_smallint.c address manipulation — where CHERIoT
# software typically uses CIncAddr/CSetAddr to position a capability cursor
# within an allocation before using it as a pointer (CTSRD/Cambridge).
# =============================================================================
#
# CSetAddr encoding (funct7=0x10, rs1=ca0=x10, rs2=a1=x11, rd=ca0=x10):
#   funct7=0b0010000, rs2=0b01011, rs1=0b01010, funct3=000, rd=0b01010
#   = 0010000_01011_01010_000_01010_1011011 = 0x20B5055B
#
# Tests:
#   1. CGetAddr after CSetAddr(0x1000) = 0x1000.
#   2. CGetBase unchanged = 0.
#   3. Tag = 1 (in-bounds, 0x1000 < 2^32).
#   4. CGetAddr after CSetAddr(0) = 0 (verify cursor can be reset).
#   5. mstatus.MIE = 1.
#   6. mcause = 0.
#   7. mip = 0.

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # Load MTCC (base=0, cursor=0, tag=1, full range).
    .word   0x03C0055B              # cspecialr ca0, mtcc

    # Set cursor to 0x1000.
    li      a1, 0x1000
    .word   0x20B5055B              # csetaddr ca0, ca0, a1

    # ── Test 1: cursor is now 0x1000 ──────────────────────────────────────────
    .word   0xFEF5055B              # cgetaddr a0, ca0
    li      a2, 0x1000
    bne     a0, a2, .Lfail_test1

    # ── Test 2: base unchanged = 0 ────────────────────────────────────────────
    .word   0xFE25055B              # cgetbase a0, ca0
    bne     a0, x0, .Lfail_test2

    # ── Test 3: tag = 1 (0x1000 within full-range MTCC) ──────────────────────
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test3

    # Set cursor back to 0.
    li      a1, 0
    .word   0x20B5055B              # csetaddr ca0, ca0, a1

    # ── Test 4: cursor back to 0 ──────────────────────────────────────────────
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
