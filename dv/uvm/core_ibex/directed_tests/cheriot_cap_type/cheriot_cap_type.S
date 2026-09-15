# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cap_type — CGetType on the three reset root capabilities
# =============================================================================
# Exercises CGetType (funct7=0x7F, rs2=1), which returns the object type of a
# capability.  All three machine-level SCR root capabilities reset with
# OTYPE_UNSEALED (3'd0).  decode_otype() in cheri_pkg.sv computes:
#   otype4 = {~perm_ex & (otype3 != 0), otype3}
# For OTYPE_UNSEALED (otype3=0): otype4 = 0 regardless of perm_ex.
# CGetType returns {28'h0, otype4} = 0 for all unsealed capabilities.
#
# The otype field distinguishes:
#   0: OTYPE_UNSEALED — a normal, usable capability
#   1: OTYPE_SENTRY   — a sealed entry point (callable but not modifiable)
#   2-3: sentry variants (forward/backward)
#
# Testing that all root SCRs return 0 confirms:
#   (1) No root capability was accidentally sealed at reset (which would
#       prevent normal use — a sealed cap cannot be modified or dereferenced).
#   (2) The cperms-to-otype pipeline initialises correctly for all three
#       capability classes (TX/TM/TS).
#
#   Test 1 (MTCC otype = 0, OTYPE_UNSEALED)
#     MTCC must be unsealed at reset — it is the trap-call capability used
#     by the hardware for control flow on exception entry.
#
#   Test 2 (MTDC otype = 0, OTYPE_UNSEALED)
#     MTDC is the data root; it must also be unsealed so it can be used as
#     a base for deriving data capabilities.
#
#   Test 3 (MScratchC otype = 0, OTYPE_UNSEALED)
#     MScratchC is the seal root; it is itself unsealed (its purpose is to
#     seal OTHER capabilities, not to be sealed itself).
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
#      cgettype writes to integer register a0, so its result is compared between
#      ibex and Spike on every step.  If the RTL encodes the wrong otype at
#      reset, Spike and the DUT diverge → cosim FAIL.
#
#   2. Self-check (bne against expected constant 0):
#      If cgettype returns anything other than 0 the branch to .Lfail_testN
#      is taken and main() returns non-zero, which the UVM testbench marks FAILED.
#
# Derived from OTYPE_UNSEALED = 3'd0 and decode_otype() in cheri_pkg.sv.
# Complements cheriot_cap_perms (which tests permissions) and cheriot_cap_base.
# =============================================================================
#
# Encodings (rd=a0=x10, rs1=ca0=x10):
#   cspecialr  ca0, mtcc      = .word 0x03C0055B  (CSpecialRW, scr=28)
#   cspecialr  ca0, mtdc      = .word 0x03D0055B  (CSpecialRW, scr=29)
#   cspecialr  ca0, mscratchc = .word 0x03E0055B  (CSpecialRW, scr=30)
#   cgettype   a0,  ca0       = .word 0xFE15055B  (funct7=0x7F, rs2=1)
#
# Tests:
#   1. MTCC otype = 0 (OTYPE_UNSEALED).
#   2. MTDC otype = 0 (OTYPE_UNSEALED).
#   3. MScratchC otype = 0 (OTYPE_UNSEALED, even though it grants sealing rights).
#   4. mstatus.MIE still = 1 after the test body (no interrupt cleared it).
#   5. mcause = 0 (no exception or interrupt was recorded).
#   6. mip = 0 (no interrupt inputs are currently asserted).

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # ── Test 1: MTCC otype = 0 (OTYPE_UNSEALED) ──────────────────────────────
    .word   0x03C0055B              # cspecialr ca0, mtcc
    .word   0xFE15055B              # cgettype  a0,  ca0
    bne     a0, x0, .Lfail_test1

    # ── Test 2: MTDC otype = 0 (OTYPE_UNSEALED) ──────────────────────────────
    .word   0x03D0055B              # cspecialr ca0, mtdc
    .word   0xFE15055B              # cgettype  a0,  ca0
    bne     a0, x0, .Lfail_test2

    # ── Test 3: MScratchC otype = 0 (OTYPE_UNSEALED) ─────────────────────────
    .word   0x03E0055B              # cspecialr ca0, mscratchc
    .word   0xFE15055B              # cgettype  a0,  ca0
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
