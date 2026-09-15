# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cap_base — base address of reset root capabilities
# =============================================================================
# Checks that the three machine-level SCR root capabilities all have base
# address = 0 at reset, using CGetBase (the first test to exercise that
# instruction, rs2=2, .word 0xFE25055B).
#
#   Test 1 (MTCC base = 0)
#     MTCC covers the full 4 GB address space starting at 0x00000000.
#     A failure means the bounds encoding for the execute root is wrong,
#     or CGetBase is misimplementing the base extraction.
#
#   Test 2 (MTDC base = 0)
#     Same check for the memory data root.  Catches a case where only one
#     of the two roots has a correct base.
#
#   Test 3 (MScratchC base = 0)
#     MScratchC is the seal root (CPERMS_TS) and also resets with base=0.
#     Exercises CGetBase on a third, different reset capability class.
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
#      cgetbase writes to integer register a0, so its result is compared
#      between ibex and Spike on every step.  If the RTL extracts the wrong
#      base from the compressed capability encoding, Spike and the DUT diverge
#      immediately → cosim FAIL.  cspecialr writes to the capability register
#      file (not directly cosim-checked); the error surfaces when the
#      subsequent cgetbase produces a non-zero integer result.
#
#   2. Self-check (bne x0 against expected value 0):
#      If cgetbase returns anything other than 0 the branch to .Lfail_testN
#      is taken and main() returns a non-zero error code, which the UVM
#      testbench detects as FAILED.
#
# Inspired by cheri-c-tests/clang_purecap_base.c (CTSRD/Cambridge).
# =============================================================================
#
# All three machine-level SCR root capabilities (MTCC, MTDC, MScratchC) are
# initialised at reset to full-range capabilities covering the entire 4 GB
# address space (base=0, length=2^32).  This test verifies base=0 for each.
#
# Uses CGetBase (funct7=0x7F, rs2=2) which has not been exercised by any
# earlier directed test.
#
# Encodings (rd=a0=x10, rs1=ca0=x10):
#   cspecialr  ca0, mtcc      = .word 0x03C0055B  (CSpecialRW, scr=28)
#   cspecialr  ca0, mtdc      = .word 0x03D0055B  (CSpecialRW, scr=29)
#   cspecialr  ca0, mscratchc = .word 0x03E0055B  (CSpecialRW, scr=30)
#   cgetbase   a0,  ca0       = .word 0xFE25055B  (funct7=0x7F, rs2=2)
#
# At reset (from cheri_pkg.sv):
#   MTCC      = MTVEC_RESET_CAP    CPERMS_TX  base=0
#   MTDC      = MTDC_RESET_CAP     CPERMS_TM  base=0
#   MScratchC = MSCRATCHC_RESET_CAP CPERMS_TS  base=0
#
# Tests:
#   1. MTCC base = 0.
#   2. MTDC base = 0.
#   3. MScratchC base = 0.
#   4. mstatus.MIE still = 1 after the test body (no interrupt cleared it).
#   5. mcause = 0 (no exception or interrupt was recorded).
#   6. mip = 0 (no interrupt inputs are currently asserted).

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # ── Test 1: MTCC base = 0 ────────────────────────────────────────────────
    .word   0x03C0055B              # cspecialr ca0, mtcc
    .word   0xFE25055B              # cgetbase  a0,  ca0
    bne     a0, x0, .Lfail_test1

    # ── Test 2: MTDC base = 0 ────────────────────────────────────────────────
    .word   0x03D0055B              # cspecialr ca0, mtdc
    .word   0xFE25055B              # cgetbase  a0,  ca0
    bne     a0, x0, .Lfail_test2

    # ── Test 3: MScratchC base = 0 ───────────────────────────────────────────
    .word   0x03E0055B              # cspecialr ca0, mscratchc
    .word   0xFE25055B              # cgetbase  a0,  ca0
    bne     a0, x0, .Lfail_test3

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
