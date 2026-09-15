# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cap_len — CGetLen on the three reset root capabilities
# =============================================================================
# Exercises CGetLen (funct7=0x7F, rs2=3), which has not been directly tested
# in isolation by any earlier directed test.  All three machine-level SCR root
# capabilities (MTCC, MTDC, MScratchC) cover the full 4 GB address space at
# reset (base=0, top=2^32).  In a 32-bit register, length = 2^32 overflows;
# get_cap_len() in cheri_pkg.sv saturates: if top33[32]=1 → return 0xFFFFFFFF.
#
#   Test 1 (MTCC length = 0xFFFFFFFF)
#     MTCC_RESET_CAP: RESETEXP=24, top9=9'h100, base=0
#     → top33 = 0x1_0000_0000, base32 = 0
#     → length = top33 - base32 = 0x1_0000_0000; top33[32]=1 → saturate
#     A failure means either the bounds encoding or CGetLen saturation is wrong.
#
#   Test 2 (MTDC length = 0xFFFFFFFF)
#     MTDC_RESET_CAP has the same RESETEXP and top9 → same result.
#
#   Test 3 (MScratchC length = 0xFFFFFFFF)
#     MSCRATCHC_RESET_CAP has the same encoding — confirming that all three
#     root capability classes apply the same full-range bounds.
#
#   Tests 4-6 (interrupt state — no interrupt expected)
#     Machine-mode interrupts are enabled at the start of the test
#     (mstatus.MIE=1).  The testbench does not assert any interrupt source
#     during this short directed test, so none should fire.
#     Test 4: mstatus.MIE still = 1 — if an interrupt had fired the hardware
#             would have cleared MIE and set MPIE during trap entry.
#     Test 5: mcause = 0 — no exception or interrupt cause recorded.
#     Test 6: mip = 0 — no interrupt inputs currently asserted.
#
# Verification:
#   Two independent layers catch a faulty DUT:
#
#   1. Cosim (Spike vs ibex RTL, per instruction step):
#      cgetlen writes to integer register a0, so its result is compared between
#      ibex and Spike on every step.  If the RTL computes the wrong length for
#      the compressed bounds encoding, Spike and the DUT diverge → cosim FAIL.
#
#   2. Self-check (bne against expected constant 0xFFFFFFFF):
#      If cgetlen returns anything other than 0xFFFFFFFF the branch to
#      .Lfail_testN is taken and main() returns a non-zero error code, which
#      the UVM testbench detects as FAILED.
#
# Inspired by cheri-c-tests/clang_purecap_null.c __builtin_cheri_length_get()
# (CTSRD/Cambridge); expected value derived from get_cap_len() in cheri_pkg.sv.
# =============================================================================
#
# Encodings (rd=a0=x10, rs1=ca0=x10):
#   cspecialr  ca0, mtcc      = .word 0x03C0055B  (CSpecialRW, scr=28)
#   cspecialr  ca0, mtdc      = .word 0x03D0055B  (CSpecialRW, scr=29)
#   cspecialr  ca0, mscratchc = .word 0x03E0055B  (CSpecialRW, scr=30)
#   cgetlen    a0,  ca0       = .word 0xFE35055B  (funct7=0x7F, rs2=3)
#
# Tests:
#   1. MTCC length = 0xFFFFFFFF (full-range saturation).
#   2. MTDC length = 0xFFFFFFFF.
#   3. MScratchC length = 0xFFFFFFFF.
#   4. mstatus.MIE still = 1 after the test body (no interrupt cleared it).
#   5. mcause = 0 (no exception or interrupt was recorded).
#   6. mip = 0 (no interrupt inputs are currently asserted).

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # ── Test 1: MTCC length = 0xFFFFFFFF ─────────────────────────────────────
    .word   0x03C0055B              # cspecialr ca0, mtcc
    .word   0xFE35055B              # cgetlen   a0,  ca0
    li      a1, -1                  # -1 = 0xFFFFFFFF as 32-bit signed
    bne     a0, a1, .Lfail_test1

    # ── Test 2: MTDC length = 0xFFFFFFFF ─────────────────────────────────────
    .word   0x03D0055B              # cspecialr ca0, mtdc
    .word   0xFE35055B              # cgetlen   a0,  ca0
    bne     a0, a1, .Lfail_test2   # a1 still -1

    # ── Test 3: MScratchC length = 0xFFFFFFFF ────────────────────────────────
    .word   0x03E0055B              # cspecialr ca0, mscratchc
    .word   0xFE35055B              # cgetlen   a0,  ca0
    bne     a0, a1, .Lfail_test3

    # ── Interrupt state verification (no interrupt expected) ──────────────────
    #
    # Test 4: mstatus.MIE still set — an interrupt clears MIE and sets MPIE on
    # trap entry, so a clear MIE here means a spurious interrupt was taken.
    csrr    a0, mstatus
    andi    a1, a0, 8               # isolate MIE (bit 3)
    beq     a1, x0, .Lfail_test4

    # Test 5: mcause = 0 — any exception or interrupt records a non-zero cause.
    csrr    a0, mcause
    bne     a0, x0, .Lfail_test5

    # Test 6: mip = 0 — reflects live interrupt input lines; must be quiescent.
    csrr    a0, mip
    bne     a0, x0, .Lfail_test6

    # ── All passed ────────────────────────────────────────────────────────────
    li      a0, 0
    ret

.Lfail_test1:
    li      a0, 1
    ret

.Lfail_test2:
    li      a0, 2
    ret

.Lfail_test3:
    li      a0, 3
    ret

.Lfail_test4:
    li      a0, 4
    ret

.Lfail_test5:
    li      a0, 5
    ret

.Lfail_test6:
    li      a0, 6
    ret
