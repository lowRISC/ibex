# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cseal_cunseal — CSeal/CUnseal round-trip on an executable cap
# =============================================================================
# CSeal (funct7=0x0b) and CUnseal (funct7=0x0c) are two-source instructions:
# cd <-- cs1 with cd.otype set from (CSeal) / cleared to (CUnseal) an
# authority provided by cs2 (ibex_cheriot_ex.sv). Sealing requires a
# dedicated "sealing capability" as cs2 -- one with Permit_Seal (SE) for
# CSeal / Permit_Unseal (US) for CUnseal, unsealed itself, tagged, and whose
# ADDRESS (not otype field) both lies within its own bounds AND encodes the
# new/expected otype value.
#
# MScratchC resets to ROOT_CAP_TS (ibex_cheriot_pkg.sv), the dedicated
# Sealing Root: cperms=CPERMS_TS expands (cheriot_expand_perms) to perm=0xE01
# (SE=1, US=1, U0=1, GL=1, all else 0) -- already verified by
# cheriot_mscratchc_seal. No other reset SCR has SE or US set.
#
# For an EXECUTABLE cs1 (MTCC, perm.EX=1), ibex_cheriot_ex.sv's
# chk_cs2_bad_type check requires cs2.address in [1,7] with bits[31:3]==0 --
# exactly the OTYPE_SENTRY_* range (1=forward, EX-only sentry). Using
# MScratchC's cursor (set via CSetAddr to 1) as cs2 avoids the more
# complicated non-executable path (whose otype range [9,15] is represented
# via an implicit 4th bit reconstructed at CGetType time from the sealed
# cap's own EX permission, not stored directly -- see
# ibex_cheriot_pkg.sv's cheriot_decode_otype).
#
#   Test 1 (tag = 1 after CSeal: cs2 checks all passed)
#   Test 2 (CGetType = 1 after CSeal: matches OTYPE_SENTRY_II_FWD)
#   Test 3 (original MTCC (cs1) untouched: still tag = 1 -- CSeal writes cd,
#           a separate register, not cs1 itself)
#   Test 4 (tag = 1 after CUnseal: cs2 checks all passed)
#   Test 5 (CGetType = 0 (OTYPE_UNSEALED) after CUnseal)
#   Test 6 (permissions preserved through the seal/unseal round trip)
#   Tests 7-9 (interrupt state — no interrupt expected)
#
# Verification: cosim (per-instruction Spike/RTL register compare) plus the
# self-check below (independent of cosim).
#
# Instruction encodings (opcode=0x5B for CHERIoT):
#   cspecialr ca0, mtcc       = .word 0x03C0055B  (rd=a0, SCR=28=MTCC)
#   cgetperm  t0, ca0         = .word 0xFE0502DB  (rs2=0x00, rs1=a0, rd=t0)
#   cspecialr ca2, mscratchc  = .word 0x03E0065B  (rd=a2, SCR=30=MSCRATCHC)
#   csetaddr  ca2,ca2,a1      = .word 0x20B6065B  (funct7=0x10, cs1=a2, rs2=a1, rd=a2)
#   cseal     ca3,ca0,ca2     = .word 0x16C506DB  (funct7=0x0b, cs1=a0, rs2=a2, rd=a3)
#   cgettag   a5, ca3         = .word 0xFE4687DB  (rs2=0x04, rs1=a3, rd=a5)
#   cgettype  a5, ca3         = .word 0xFE1687DB  (rs2=0x01, rs1=a3, rd=a5)
#   cgettag   a5, ca0         = .word 0xFE4507DB  (rs2=0x04, rs1=a0, rd=a5)
#   cunseal   ca4,ca3,ca2     = .word 0x18C6875B  (funct7=0x0c, cs1=a3, rs2=a2, rd=a4)
#   cgettag   a5, ca4         = .word 0xFE4707DB  (rs2=0x04, rs1=a4, rd=a5)
#   cgettype  a5, ca4         = .word 0xFE1707DB  (rs2=0x01, rs1=a4, rd=a5)
#   cgetperm  a5, ca4         = .word 0xFE0707DB  (rs2=0x00, rs1=a4, rd=a5)

.globl main
main:
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # a0 = MTCC (execute root: perms=0x1EB (EX=1,GL=1,...), tag=1, unsealed)
    .word   0x03C0055B              # cspecialr ca0, mtcc
    .word   0xFE0502DB              # cgetperm t0, ca0   -> save original perms

    # a2 = MScratchC (sealing root: perms=0xE01 (SE=1,US=1), tag=1, unsealed),
    # cursor set to 1 (OTYPE_SENTRY_II_FWD) -- both the sealing authority AND
    # the otype value to seal with.
    .word   0x03E0065B              # cspecialr ca2, mscratchc
    li      a1, 1
    .word   0x20B6065B              # csetaddr ca2, ca2, a1

    # Seal a0 (MTCC) into a3 using a2 as the sealing authority.
    .word   0x16C506DB              # cseal ca3, ca0, ca2

    # ── Test 1: tag = 1 (all CSeal permission/bound checks passed) ───────────
    .word   0xFE4687DB              # cgettag a5, ca3
    li      a4, 1
    bne     a5, a4, .Lfail_test1

    # ── Test 2: otype = 1 (OTYPE_SENTRY_II_FWD) ───────────────────────────────
    .word   0xFE1687DB              # cgettype a5, ca3
    bne     a5, a4, .Lfail_test2    # a4 still holds 1

    # ── Test 3: original a0 (cs1) untouched by CSeal -- still tag = 1 ────────
    .word   0xFE4507DB              # cgettag a5, ca0
    bne     a5, a4, .Lfail_test3

    # Unseal a3 back using the same sealing authority (a2 also has US=1).
    .word   0x18C6875B              # cunseal ca4, ca3, ca2

    # ── Test 4: tag = 1 (all CUnseal permission/bound checks passed) ─────────
    .word   0xFE4707DB              # cgettag a5, ca4
    bne     a5, a4, .Lfail_test4

    # ── Test 5: otype = 0 (OTYPE_UNSEALED) ────────────────────────────────────
    .word   0xFE1707DB              # cgettype a5, ca4
    bnez    a5, .Lfail_test5

    # ── Test 6: permissions preserved through the round trip ────────────────
    .word   0xFE0707DB              # cgetperm a5, ca4
    bne     a5, t0, .Lfail_test6

    # ── Interrupt state verification ───────────────────────────────────────────
    csrr    a0, mstatus
    andi    a1, a0, 8
    beq     a1, x0, .Lfail_test7
    csrr    a0, mcause
    bne     a0, x0, .Lfail_test8
    csrr    a0, mip
    bne     a0, x0, .Lfail_test9

    li      a0, 0
    ret

.Lfail_test1: li a0, 1; ret
.Lfail_test2: li a0, 2; ret
.Lfail_test3: li a0, 3; ret
.Lfail_test4: li a0, 4; ret
.Lfail_test5: li a0, 5; ret
.Lfail_test6: li a0, 6; ret
.Lfail_test7: li a0, 7; ret
.Lfail_test8: li a0, 8; ret
.Lfail_test9: li a0, 9; ret
