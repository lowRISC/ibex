# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cap_perms — code vs data capability permission bits at reset
# =============================================================================
# Checks that the two main reset root capabilities carry the correct
# architectural permission sets, using cgetperm.
#
#   Tests 1-2 (MTCC — execute root, CPERMS_TX, expected perms=0x1EB)
#     MTCC is the machine trap-call capability and must be executable.
#     Test 1: tag=1 (it is a valid capability).
#     Test 2: permit_execute (bit 8) is SET — MTCC is a code capability.
#     A failure in test 2 means the execute-class permission encoding
#     (CPERMS_TX → expand_perms → EX bit) is broken.
#
#   Tests 3-6 (MTDC — memory data root, CPERMS_TM, expected perms=0x07F)
#     MTDC is the machine trap-data capability and must NOT be executable.
#     Test 3: tag=1 (it is a valid capability).
#     Test 4: permit_execute (bit 8) is CLEAR — MTDC is a data capability.
#     Test 5: permit_load   (bit 5) is SET   — reads are allowed.
#     Test 6: permit_store  (bit 2) is SET   — writes are allowed.
#     A failure distinguishes between wrong permissions and a missing tag.
#
#   Tests 7-9 (interrupt state — no interrupt expected)
#     Machine-mode interrupts are enabled at the start of the test
#     (mstatus.MIE=1).  The testbench does not assert any interrupt source
#     during this short directed test, so none should fire.
#     Test 7: mstatus.MIE still = 1 — if an interrupt had fired the hardware
#             would have cleared MIE and set MPIE during trap entry.
#     Test 8: mcause = 0 — no exception or interrupt cause recorded.
#     Test 9: mip = 0 — no interrupt inputs currently asserted.
#
# Verification:
#   Two independent layers catch a faulty DUT:
#
#   1. Cosim (Spike vs ibex RTL, per instruction step):
#      cgetperm and cgettag both write to integer register a0, so each result
#      is compared between ibex and Spike on every step.  A wrong permission
#      encoding in the RTL (e.g. EX bit clear for MTCC, or EX bit set for MTDC)
#      causes a Spike vs DUT divergence → cosim FAIL.
#      cspecialr writes to the capability register file (not directly cosim-
#      checked); the error is exposed when the subsequent cgetperm returns the
#      wrong permission word.
#
#   2. Self-check (andi + bne/beq against known expected bits):
#      Each sub-test masks a specific permission bit with andi and branches to
#      a numbered fail label if the bit is wrong.  main() returning non-zero
#      causes the UVM testbench to mark the run as FAILED.
#
# Inspired by cheri-c-tests/clang_purecap_init.c (CTSRD/Cambridge).
# =============================================================================
# verifies that code capabilities have execute permission and data
# capabilities do not.
#
# Uses raw .word-encoded CHERIoT instructions compiled via the standard
# rv32imc GCC toolchain.
#
# Encodings confirmed with CHERIoT LLVM 20.0.0 and verified against the
# CHERIoT sail model (src/cheri_insts.sail encdec clauses):
#   cspecialr ca0, mtcc  = .word 0x03C0055B  (CSpecialRW funct7=0x01, scr=28)
#   cspecialr ca0, mtdc  = .word 0x03D0055B  (CSpecialRW funct7=0x01, scr=29)
#   cgettag   a0,  ca0   = .word 0xFE45055B  (CGetTag  funct7=0x7F, rs2=4)
#   cgetperm  a0,  ca0   = .word 0xFE05055B  (CGetPerm funct7=0x7F, rs2=0)
#
# Permission bitmap returned by cgetperm (12 bits, bit 0 = LSB):
#   bit  0: global
#   bit  1: permit_load_global
#   bit  2: permit_store
#   bit  3: permit_load_mutable
#   bit  4: permit_store_local_cap
#   bit  5: permit_load
#   bit  6: permit_load_store_cap
#   bit  7: access_system_regs
#   bit  8: permit_execute           ← the key bit for code vs data caps
#   bits 9-11: permit_unseal/permit_seal/perm_user0
#
# At reset (from cheri_pkg.sv):
#   MTCC = MTVEC_RESET_CAP  CPERMS_TX  perms = 0x1EB  (execute root)
#   MTDC = MTDC_RESET_CAP   CPERMS_TM  perms = 0x07F  (memory data root)
#
# Tests:
#   1. MTCC has tag = 1 (it is a valid capability).
#   2. MTCC has permit_execute (bit 8); it is a code capability.
#   3. MTDC has tag = 1 (it is a valid capability).
#   4. MTDC does NOT have permit_execute (bit 8); it is a data capability.
#   5. MTDC has permit_load (bit 5).
#   6. MTDC has permit_store (bit 2).
#   7. mstatus.MIE still = 1 after the test body (no interrupt cleared it).
#   8. mcause = 0 (no exception or interrupt was recorded).
#   9. mip = 0 (no interrupt inputs are currently asserted).

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # ── Test 1: MTCC is a valid capability (tag = 1) ──────────────────────
    #
    # MTCC (machine trap-call capability, SCR 28) is set at reset to a
    # valid full-range code capability (tag = 1).
    .word   0x03C0055B              # cspecialr ca0, mtcc
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test1

    # ── Test 2: MTCC has execute permission (bit 8) ───────────────────────
    #
    # MTCC is the execution root; cgetperm must return a value with bit 8
    # set.  At reset perms = 0x1EB = 0b0001_1110_1011.
    .word   0xFE05055B              # cgetperm a0, ca0
    andi    a1, a0, 0x100           # isolate permit_execute (bit 8)
    beq     a1, x0, .Lfail_test2

    # ── Test 3: MTDC is a valid capability (tag = 1) ──────────────────────
    #
    # MTDC (machine trap-data capability, SCR 29) is set at reset to a
    # valid full-range data capability (tag = 1).
    .word   0x03D0055B              # cspecialr ca0, mtdc
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test3

    # ── Test 4: MTDC does NOT have execute permission (it is a data cap) ──
    #
    # MTDC is the memory data root; it must NOT be executable.
    # At reset perms = 0x07F = 0b0000_0111_1111.
    .word   0xFE05055B              # cgetperm a0, ca0
    andi    a1, a0, 0x100           # isolate permit_execute (bit 8)
    bne     a1, x0, .Lfail_test4

    # ── Test 5: MTDC has load permission (bit 5) ──────────────────────────
    andi    a1, a0, 0x20            # isolate permit_load (bit 5)
    beq     a1, x0, .Lfail_test5

    # ── Test 6: MTDC has store permission (bit 2) ─────────────────────────
    andi    a1, a0, 0x4             # isolate permit_store (bit 2)
    beq     a1, x0, .Lfail_test6

    # ── Interrupt state verification (no interrupt expected) ──────────────
    #
    # Test 7: mstatus.MIE still set — an interrupt clears MIE and sets MPIE on
    # trap entry, so a clear MIE here means a spurious interrupt was taken.
    csrr    a0, mstatus
    andi    a1, a0, 8               # isolate MIE (bit 3)
    beq     a1, x0, .Lfail_test7

    # Test 8: mcause = 0 — any exception or interrupt records a non-zero cause.
    csrr    a0, mcause
    bne     a0, x0, .Lfail_test8

    # Test 9: mip = 0 — reflects live interrupt input lines; must be quiescent.
    csrr    a0, mip
    bne     a0, x0, .Lfail_test9

    # ── All passed ────────────────────────────────────────────────────────
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

.Lfail_test9:
    li      a0, 9
    ret
