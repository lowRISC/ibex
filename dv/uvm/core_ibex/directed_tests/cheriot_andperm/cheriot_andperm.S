# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_andperm — CAndPerm narrows permissions without clearing tag
# =============================================================================
# CAndPerm (funct7=0x0D in the CHERIoT custom-2 R-type space) applies a
# bitwise AND to the architectural permission field of a capability.
#
# cheri_ex.sv implementation:
#   tfcap.perms = tfcap.perms & rf_rdata_b[PERMS_W-1:0];
#   pmask[PERM_GL] = 1'b1;   // treat GL as always 1 in the sealed-tag check
#   tfcap.valid = valid & (~is_cap_sealed(cs1) | (&pmask));
#   // For unsealed caps: is_cap_sealed = 0, so valid = valid & 1 = valid.
#
# Key insight: CAndPerm on an UNSEALED capability always preserves the tag.
# This is correct by design — narrowing permissions must be safe (monotone
# capability derivation).  Only sealing/unsealing involves otype checks.
#
#   Test 1 (tag preserved after CAndPerm)
#     Start with MTCC (tag=1).  Apply mask 0xFF (bits 7:0 only, clearing
#     EX=bit8 and above).  The capability is unsealed → tag stays 1.
#
#   Test 2 (EX permission is cleared)
#     MTCC has permit_execute (EX, bit 8) = 1.  After CAndPerm(0xFF),
#     EX must be 0.  A failure means CAndPerm is not masking correctly.
#
#   Test 3 (GL permission is preserved)
#     MTCC has global (GL, bit 0) = 1.  Mask 0xFF includes bit 0 → GL
#     is preserved.  This verifies that CAndPerm doesn't clear bits that
#     the mask leaves set.
#
#   Tests 4-6 (interrupt state — no interrupt expected)
#     Machine-mode interrupts are enabled at the start of the test
#     (mstatus.MIE=1).  The testbench does not assert any interrupt source
#     during this short directed test, so none should fire.
#     Test 4: mstatus.MIE still = 1.
#     Test 5: mcause = 0.
#     Test 6: mip = 0.
#
# Verification:
#   Two independent layers catch a faulty DUT:
#
#   1. Cosim (Spike vs ibex RTL, per instruction step):
#      cgettag and cgetperm write to integer register a0, so their results
#      are compared between ibex and Spike on every step.  If CAndPerm does
#      not apply the mask correctly, the subsequent cgetperm will diverge.
#
#   2. Self-check (andi + bne/beq against known expected bit values):
#      Test 1 checks tag via cgettag.  Tests 2-3 check specific bits of the
#      permission word via andi + branch.  main() returning non-zero = FAILED.
#
# Inspired by cheri-c-tests/clang_purecap_init.c ASSERT_HAS_NOT_PERMISSION /
# ASSERT_HAS_PERMISSION checks (CTSRD/Cambridge).
# =============================================================================
#
# CAndPerm encoding (funct7=0x0D, rs1=ca0=x10, rs2=a1=x11, rd=ca0=x10):
#   funct7=0b0001101, rs2=0b01011, rs1=0b01010, funct3=000, rd=0b01010
#   = 0001101_01011_01010_000_01010_1011011 = 0x1AB5055B
#
# Permission bits in MTCC (CPERMS_TX, perms=0x1EB = 0b0001_1110_1011):
#   bit 0: GL (global)           = 1
#   bit 1: LG (load-global)      = 1
#   bit 3: LM (load-mutable)     = 1
#   bit 5: LD (permit_load)      = 1
#   bit 6: MC (load-store-cap)   = 1
#   bit 7: SR (access-sys-regs)  = 1
#   bit 8: EX (permit_execute)   = 1
# After CAndPerm(mask=0xFF): EX(bit8)=0, GL(bit0)=1, others 0-7 unchanged.
#
# Tests:
#   1. tag still = 1 after CAndPerm on MTCC with mask 0xFF.
#   2. EX (bit 8) = 0 after the mask (it was 1 in MTCC, mask excluded it).
#   3. GL (bit 0) = 1 (mask 0xFF includes bit 0, so GL is preserved).
#   4. mstatus.MIE = 1.
#   5. mcause = 0.
#   6. mip = 0.

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # Load MTCC (perms=0x1EB, EX=1, tag=1).
    .word   0x03C0055B              # cspecialr ca0, mtcc

    # Apply CAndPerm with mask 0xFF (clears bits 8-11, keeps bits 0-7).
    li      a1, 0xFF                # mask: bits 7:0 only
    .word   0x1AB5055B              # candperm ca0, ca0, a1

    # ── Test 1: tag still = 1 (CAndPerm on unsealed cap preserves tag) ────────
    .word   0xFE45055B              # cgettag a0, ca0
    li      a2, 1
    bne     a0, a2, .Lfail_test1

    # ── Test 2: EX (bit 8) is now clear ──────────────────────────────────────
    .word   0xFE05055B              # cgetperm a0, ca0
    andi    a1, a0, 0x100           # isolate EX (bit 8)
    bne     a1, x0, .Lfail_test2   # EX must be 0

    # ── Test 3: GL (bit 0) is still set ──────────────────────────────────────
    andi    a1, a0, 0x1             # isolate GL (bit 0)
    beq     a1, x0, .Lfail_test3   # GL must still be 1

    # ── Interrupt state verification (no interrupt expected) ──────────────────
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
