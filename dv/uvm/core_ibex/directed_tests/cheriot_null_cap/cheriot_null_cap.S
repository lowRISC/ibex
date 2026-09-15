# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_null_cap — null capability and reset tag sanity
# =============================================================================
# Checks the most fundamental CHERIoT property: the capability tag bit is
# managed correctly by the hardware.
#
#   Test 1 (integer zero → tag=0)
#     Writing an integer value into a register clears its capability tag.
#     The zero register in capability context must return tag=0 ("null
#     capability").  A failure here means the tag clear logic is broken.
#
#   Test 2 (MTCC → tag=1)
#     MTCC (machine trap-call capability, SCR 28) must be a valid capability
#     at reset.  A failure means the SCR reset initialisation is missing or
#     the tag is not propagated through cspecialr.
#
#   Test 3 (MTDC → tag=1)
#     MTDC (machine data capability, SCR 29) must be valid at reset.
#     ibex CHERIoT does not implement DDC (SCR addresses < 27 are illegal);
#     MTDC is the data root capability and is the relevant reset check.
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
#      cgettag writes to an integer register (a0), so its result is compared
#      between ibex and Spike on every step.  If the RTL returns the wrong
#      tag value, Spike and the DUT diverge immediately → cosim FAIL.
#      Note: cspecialr writes to the capability register file, which is not
#      directly in the cosim's integer-register view; the error surfaces when
#      a subsequent cgettag produces the wrong integer result.
#
#   2. Self-check (bne / expected constant):
#      If the tag value does not match the expected constant (0 or 1), the
#      branch to .Lfail_testN is taken and main() returns a non-zero error
#      code.  The UVM testbench detects a non-zero return as FAILED.
#
# Adapted from cheri-c-tests/clang_purecap_null.c (CTSRD/Cambridge).
# =============================================================================
#
# Tests fundamental capability properties using raw .word-encoded CHERIoT
# instructions.  Compiled with the standard rv32imc GCC toolchain; the .word
# directives embed the CHERIoT instruction encodings directly.
#
# Encodings confirmed with CHERIoT LLVM 20.0.0 / ibex cheri_pkg.sv:
#   cspecialr ca0, mtcc  = .word 0x03C0055B  (SCR 28 = MTCC)
#   cspecialr ca0, mtdc  = .word 0x03D0055B  (SCR 29 = MTDC)
#   cgettag   a0,  ca0   = .word 0xFE45055B
#
# Note: ibex CHERIoT does not implement DDC.  Valid SCR addresses are
#   27=ZTOP, 28=MTCC, 29=MTDC, 30=MScratchC, 31=MEPCC.  Access to
#   SCR < 27 faults with illegal_scr_addr.
#
# Used with the 'cheriot-c-tests' directed test config (crt_cheriot.S startup,
# syscalls.c pass/fail via SIGNATURE_ADDR write).  main() returning 0 = pass.
#
# Tests:
#   1. An integer-zero register has capability tag = 0 (null, untagged).
#   2. The machine trap-call capability (MTCC) has tag = 1 (valid).
#   3. The machine data capability (MTDC) has tag = 1 (valid).
#   4. mstatus.MIE still = 1 after the test body (no interrupt cleared it).
#   5. mcause = 0 (no exception or interrupt was recorded).
#   6. mip = 0 (no interrupt inputs are currently asserted).

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # ── Test 1: integer zero has no capability tag (tag = 0) ──────────────
    #
    # li a0, 0 → addi a0, x0, 0: integer ALU clears the capability tag of rd.
    # cgettag a0, ca0: reads the tag bit of a0 (in capability context).
    # Expected: a0 = 0 (null, no capability).
    li      a0, 0
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test1

    # ── Test 2: MTCC is a valid capability (tag = 1) ──────────────────────
    #
    # MTCC (machine trap-call capability, SCR 28) is set by the hardware at
    # reset to a valid full-range code capability (tag = 1).
    .word   0x03C0055B              # cspecialr ca0, mtcc
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test2

    # ── Test 3: MTDC is a valid capability (tag = 1) ─────────────────────
    #
    # MTDC (machine data capability, SCR 29) is set at reset to a valid
    # full-range data capability (tag = 1).  ibex CHERIoT has no DDC CSR;
    # MTDC is the data root equivalent.
    .word   0x03D0055B              # cspecialr ca0, mtdc  (SCR 29)
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test3

    # ── Interrupt state verification (no interrupt expected) ──────────────
    #
    # MIE was set at entry.  Since the testbench does not assert any interrupt
    # source during this short directed test, no interrupt should have fired.
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
