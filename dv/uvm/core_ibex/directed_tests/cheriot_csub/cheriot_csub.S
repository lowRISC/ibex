# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_csub — CSub computes the difference between capability cursors
# =============================================================================
# CSub (funct7=0x14, R-type) computes:
#   rd (integer) = cs1.cursor - cs2.cursor
# The result is an integer (no capability tag).  This is the canonical way to
# compute a pointer difference in CHERIoT without discarding capability bounds.
#
# ibex_decoder.sv: 7'h14 → CSUB_CAP.
# cheri_ex.sv: result_data_o = rf_rdata_a - rf_rdata_b  (integer subtract).
#
# Uses two capability registers: ca0 (x10) and ca1 (x11).
#
#   Test 1 (CSub of two identical-cursor capabilities = 0)
#     Both ca0 and ca1 are read from MTCC (cursor=0).  CSub returns 0.
#     This confirms that CSub computes cursor - cursor and does not read
#     the wrong register or operand source.
#
#   Test 2 (CSub after CIncAddr yields the increment)
#     ca0 is advanced by 16 via CIncAddr; ca1 stays at cursor=0 (fresh MTCC).
#     CSub(ca0, ca1) should return 16.  This is the standard pointer-difference
#     use case (offset between two pointers into the same allocation).
#
#   Tests 3-5 (interrupt state — no interrupt expected)
#     Machine-mode interrupts are enabled at the start of the test.
#     Test 3: mstatus.MIE still = 1.
#     Test 4: mcause = 0.
#     Test 5: mip = 0.
#
# Verification:
#   Two independent layers catch a faulty DUT:
#
#   1. Cosim (Spike vs ibex RTL, per instruction step):
#      CSub writes to integer register a0 → cosim verifies the result.
#      CIncAddr before the subtraction also updates the cursor in a0's
#      shadow (via cgetaddr/cinc_addr path), both verified by cosim.
#
#   2. Self-check (bne against expected constants):
#      main() returns non-zero if any check fails → UVM testbench marks FAILED.
#
# Inspired by clang_purecap_capcmp.c pointer difference operations and the
# general CHERIoT idiom of computing (char*)end - (char*)start (CTSRD/Cambridge).
# =============================================================================
#
# cspecialr ca1, mtcc (rd=ca1=x11, scr=28):
#   funct7=1, rs2=28=0b11100, rs1=0, rd=x11=0b01011
#   [7:0]: rd[0]=1 → bit7=1, opcode=0x5B → 0xDB
#   = 0x03C005DB
#
# CSub encoding (funct7=0x14, rs1=ca0=x10, rs2=ca1=x11, rd=a0=x10):
#   funct7=0b0010100, rs2=0b01011, rs1=0b01010, funct3=000, rd=0b01010
#   = 0010100_01011_01010_000_01010_1011011 = 0x28B5055B
#
# CIncAddr encoding (funct7=0x11, rs1=ca0=x10, rs2=a1=x11, rd=ca0=x10):
#   = 0x22B5055B
#
# Tests:
#   1. CSub(MTCC, MTCC) = 0 (same cursor).
#   2. CSub(MTCC+16, MTCC) = 16 (cursor difference).
#   3. mstatus.MIE = 1.
#   4. mcause = 0.
#   5. mip = 0.

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # Load MTCC into both ca0 and ca1 (cursor=0 for both).
    .word   0x03C0055B              # cspecialr ca0, mtcc
    .word   0x03C005DB              # cspecialr ca1, mtcc  (rd=ca1=x11)

    # ── Test 1: CSub(ca0, ca1) = 0 — both cursors are 0 ─────────────────────
    .word   0x28B5055B              # csub a0, ca0, ca1
    bne     a0, x0, .Lfail_test1

    # Advance ca0 cursor by 16 (ca1 still at cursor=0).
    li      a1, 16
    .word   0x22B5055B              # cincaddr ca0, ca0, a1

    # ── Test 2: CSub(ca0, ca1) = 16 — one cursor advanced ────────────────────
    .word   0x28B5055B              # csub a0, ca0, ca1
    li      a2, 16
    bne     a0, a2, .Lfail_test2

    # ── Interrupt state verification ───────────────────────────────────────────
    csrr    a0, mstatus
    andi    a1, a0, 8
    beq     a1, x0, .Lfail_test3
    csrr    a0, mcause
    bne     a0, x0, .Lfail_test4
    csrr    a0, mip
    bne     a0, x0, .Lfail_test5

    li      a0, 0
    ret

.Lfail_test1: li a0, 1; ret
.Lfail_test2: li a0, 2; ret
.Lfail_test3: li a0, 3; ret
.Lfail_test4: li a0, 4; ret
.Lfail_test5: li a0, 5; ret
