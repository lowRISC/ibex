# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_mscratchc_seal — MScratchC is the seal root at reset
# =============================================================================
# MScratchC (SCR 30) is not a general-purpose scratch register in CHERIoT-Ibex:
# it resets to CPERMS_TS (6'b100111), the seal root capability.  The seal root
# grants the right to seal and unseal capabilities — a distinct permission class
# from code (MTCC/CPERMS_TX) and data (MTDC/CPERMS_TM) roots.
#
# expand_perms(CPERMS_TS) yields 0xE01:
#   bit  0 (GL, global)         = 1  — it is a global capability
#   bit  9 (US, permit_unseal)  = 1  — can unseal sealed objects
#   bit 10 (SE, permit_seal)    = 1  — can seal capabilities (primary purpose)
#   bit 11 (U0, user-defined 0) = 1  — set by the seal-class encoding
#   all other bits              = 0  — in particular EX (bit 8) is CLEAR
#
#   Test 1 (tag = 1)
#     MScratchC must be a valid capability at reset.
#
#   Test 2 (permit_seal, bit 10, is SET)
#     The core function of the seal root: confirms the SE bit survives the
#     cperms compression/expansion round-trip through expand_perms().
#
#   Test 3 (permit_unseal, bit 9, is SET)
#     Paired with SE: the seal root can also unseal.
#
#   Test 4 (permit_execute, bit 8, is CLEAR)
#     MScratchC must NOT be an execute capability.  If EX were set, it would
#     indicate a wrong cperms class was applied to this SCR at reset.
#
#   Test 5 (global, bit 0, is SET)
#     All CHERIoT root capabilities are global (bit 5 of cperms → PERM_GL).
#
#   Tests 6-8 (interrupt state — no interrupt expected)
#     Machine-mode interrupts are enabled at the start of the test
#     (mstatus.MIE=1).  The testbench does not assert any interrupt source
#     during this short directed test, so none should fire.
#     Test 6: mstatus.MIE still = 1 — if an interrupt had fired the hardware
#             would have cleared MIE and set MPIE during trap entry.
#     Test 7: mcause = 0 — no exception or interrupt cause recorded.
#     Test 8: mip = 0 — no interrupt inputs currently asserted.
#
# Verification:
#   Two independent layers catch a faulty DUT:
#
#   1. Cosim (Spike vs ibex RTL, per instruction step):
#      cgettag and cgetperm both write to integer register a0, so each result
#      is compared between ibex and Spike on every step.  If the RTL assigns
#      the wrong cperms class to MScratchC at reset (e.g. CPERMS_TM instead of
#      CPERMS_TS), the cgetperm result will differ from Spike → cosim FAIL.
#      cspecialr writes to the capability register file (not directly cosim-
#      checked); the error surfaces when cgettag/cgetperm return wrong values.
#
#   2. Self-check (andi + bne/beq against known expected bits):
#      Each sub-test masks a specific bit with andi and branches to a numbered
#      fail label if the bit is wrong.  main() returning non-zero causes the
#      UVM testbench to mark the run as FAILED.  Test 4 in particular would
#      catch a case where MScratchC was accidentally given execute permission.
#
# Inspired by cheri-c-tests/clang_purecap_init.c (CTSRD/Cambridge);
# MScratchC as seal root is specific to CHERIoT-Ibex (cheri_pkg.sv).
# =============================================================================
#
# MScratchC (SCR 30) is initialised at reset to CPERMS_TS (6'b100111) — the
# seal root capability.  Decoding via expand_perms() in cheri_pkg.sv:
#   cperms[5]=1  → PERM_GL  (bit  0)
#   cperms[4:3]=0b00 → seal class:
#     cperms[0]=1 → PERM_US  (bit  9)   permit_unseal
#     cperms[1]=1 → PERM_SE  (bit 10)   permit_seal
#     cperms[2]=1 → PERM_U0  (bit 11)   user-defined 0
#
# Expected cgetperm value: 0xE01 = 0b1110_0000_0001
#   Bits set: GL(0)=1, US(9)=1, SE(10)=1, U0(11)=1
#   Bits clear: all others including EX(8)=0 (NOT executable)
#
# Encodings (rd=a0=x10, rs1=ca0=x10):
#   cspecialr  ca0, mscratchc = .word 0x03E0055B  (CSpecialRW, scr=30)
#   cgettag    a0,  ca0       = .word 0xFE45055B  (funct7=0x7F, rs2=4)
#   cgetperm   a0,  ca0       = .word 0xFE05055B  (funct7=0x7F, rs2=0)
#
# Tests:
#   1. MScratchC is a valid capability (tag = 1).
#   2. permit_seal   (bit 10) is set   — it is the seal root.
#   3. permit_unseal (bit  9) is set   — can unseal sealed objects.
#   4. permit_execute (bit 8) is clear — NOT an execute capability.
#   5. global        (bit  0) is set   — it is a global capability.
#   6. mstatus.MIE still = 1 after the test body (no interrupt cleared it).
#   7. mcause = 0 (no exception or interrupt was recorded).
#   8. mip = 0 (no interrupt inputs are currently asserted).

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    .word   0x03E0055B              # cspecialr ca0, mscratchc

    # ── Test 1: tag = 1 (valid capability) ───────────────────────────────────
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test1

    # Read permissions once; tests 2-5 all inspect this value.
    .word   0xFE05055B              # cgetperm a0, ca0

    # ── Test 2: permit_seal (bit 10) is set ──────────────────────────────────
    andi    a1, a0, 0x400           # isolate SE
    beq     a1, x0, .Lfail_test2

    # ── Test 3: permit_unseal (bit 9) is set ─────────────────────────────────
    andi    a1, a0, 0x200           # isolate US
    beq     a1, x0, .Lfail_test3

    # ── Test 4: NOT permit_execute (bit 8 must be clear) ─────────────────────
    andi    a1, a0, 0x100           # isolate EX
    bne     a1, x0, .Lfail_test4

    # ── Test 5: global (bit 0) is set ────────────────────────────────────────
    andi    a1, a0, 0x1             # isolate GL
    beq     a1, x0, .Lfail_test5

    # ── Interrupt state verification (no interrupt expected) ──────────────────
    #
    # Test 6: mstatus.MIE still set — an interrupt clears MIE and sets MPIE on
    # trap entry, so a clear MIE here means a spurious interrupt was taken.
    csrr    a0, mstatus
    andi    a1, a0, 8               # isolate MIE (bit 3)
    beq     a1, x0, .Lfail_test6

    # Test 7: mcause = 0 — any exception or interrupt records a non-zero cause.
    csrr    a0, mcause
    bne     a0, x0, .Lfail_test7

    # Test 8: mip = 0 — reflects live interrupt input lines; must be quiescent.
    csrr    a0, mip
    bne     a0, x0, .Lfail_test8

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

.Lfail_test7:
    li      a0, 7
    ret

.Lfail_test8:
    li      a0, 8
    ret
