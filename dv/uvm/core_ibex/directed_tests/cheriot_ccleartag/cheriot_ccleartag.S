# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_ccleartag — CClearTag explicitly revokes the capability tag
# =============================================================================
# CClearTag (funct7=0x7F, rs2=0x0B in the CGet decode block of ibex_decoder.sv)
# returns the same capability value but with tag = 0.  This is the explicit
# capability revocation instruction — used when software wants to pass a
# reference to data that carries the same address/bounds as a valid capability
# but must not be treated as one (e.g., when communicating with untrusted code).
#
# cheri_ex.sv: CCLEAR_TAG: result_data_o = rf_rdata_a; result_cap_o = cap with
# valid=0.  The integer address is preserved; only the tag bit is cleared.
#
#   Test 1 (MTCC tag starts at 1, before CClearTag)
#     Confirm the starting state is tag=1.  This rules out the possibility
#     that the tag was already 0 before the instruction ran.
#
#   Test 2 (tag is 0 after CClearTag)
#     After CClearTag, cgettag must return 0.  A failure means CClearTag is
#     either not decoded, or the tag-clear logic is not writing the result back.
#
#   Test 3 (the integer address value is unchanged after CClearTag)
#     CClearTag must NOT modify the address portion.  MTCC address=0 at reset.
#     If the address changes, the instruction is also corrupting data.
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
#      cgettag and cgetaddr write to integer register a0 → cosim verifies each
#      result.  If CClearTag does not clear the tag, the subsequent cgettag
#      returns 1 in the DUT but 0 in Spike → cosim FAIL.
#
#   2. Self-check (bne/beq against expected constants):
#      main() returns non-zero if any check fails → UVM testbench marks FAILED.
#
# Relevant to clang_purecap_null.c and any test that checks that integer
# values do not have capability tags (CTSRD/Cambridge).  CClearTag is the
# deliberate instruction-level counterpart to the automatic tag-clearing that
# happens with integer ALU operations (tested in cheriot_intcap_arith).
# =============================================================================
#
# CClearTag encoding (funct7=0x7F, rs2=0x0B, rs1=ca0=x10, rd=ca0=x10):
#   funct7=0b1111111, rs2=0b01011, rs1=0b01010, funct3=000, rd=0b01010
#   = 1111111_01011_01010_000_01010_1011011 = 0xFEB5055B
#
# Tests:
#   1. Before CClearTag: MTCC tag = 1.
#   2. After  CClearTag: ca0 tag = 0.
#   3. After  CClearTag: ca0 address = 0 (address unchanged by CClearTag).
#   4. mstatus.MIE = 1.
#   5. mcause = 0.
#   6. mip = 0.

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # Load MTCC (tag=1, address=0).
    .word   0x03C0055B              # cspecialr ca0, mtcc

    # ── Test 1: tag = 1 before CClearTag ──────────────────────────────────────
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test1

    # Apply CClearTag.
    .word   0xFEB5055B              # ccleartag ca0, ca0

    # ── Test 2: tag = 0 after CClearTag ───────────────────────────────────────
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test2   # tag must be 0

    # ── Test 3: address unchanged (still 0) ───────────────────────────────────
    .word   0xFEF5055B              # cgetaddr a0, ca0
    bne     a0, x0, .Lfail_test3   # address must still be 0

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
