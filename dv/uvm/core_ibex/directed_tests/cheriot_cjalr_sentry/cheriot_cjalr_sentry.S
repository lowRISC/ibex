# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cjalr_sentry — CJALR compartment call/return via a sentry
# =============================================================================
# CJALR reuses the plain RISC-V JALR opcode/encoding (ibex_decoder.sv,
# OPCODE_JALR case): under cheriot_enable_i it always routes through
# cheriot_ex as CJALR instead of the generic jump datapath (see REQ_CFI_06 --
# jump_in_dec is never asserted in this mode). No custom .word encoding is
# needed here; plain `jalr` assembles to exactly the instruction the decoder
# expects.
#
# All prior CHERIoT directed tests only exercise CJALR *implicitly*, through
# `ret`/tail-call codegen in crt boot code -- always an unsealed-capability
# jump with rd=x0. This test exercises the actual sentry mechanics
# (ibex_cheriot_ex.sv, CJALR case + the CJALR branch of the perm_vio_vec
# always_comb block), which only fire when rd=ra and cs1 is an
# interrupt-toggling forward sentry (OTYPE_SENTRY_ID_FWD=2 / IE_FWD=3):
#
#   - Jumping through ANY cs1 unseals it into PCC (`pcc_cap_o =
#     cheriot_unseal(rf_fullcap_a)`) -- entering a sentry always yields
#     ordinary executable PCC.
#   - If rd==ra(x1), the link capability is ALWAYS freshly sealed as a
#     backward sentry (OTYPE_SENTRY_IE_BKWD if mstatus.MIE was 1 at the call,
#     otherwise ID_BKWD) -- regardless of whether cs1 itself was a sentry.
#   - csr_set_mie_raw/csr_clr_mie_raw fire ONLY for interrupt-toggling
#     sentries (otype 2/3 forward, 4/5 backward): entering via IE_FWD/IE_BKWD
#     sets mstatus.MIE; ID_FWD/ID_BKWD clears it. Matches REQ_INT_07's
#     documented behaviour, exercised here directly for the first time.
#   - `jalr x0, ra, 0` back through the auto-generated backward sentry then
#     restores mstatus.MIE to whatever it was at the original call time --
#     the save/restore round trip a real compartment call relies on.
#
# Construction: seal MTCC's cursor-adjusted copy (pointing at .Lcallee) using
# MScratchC (ROOT_CAP_TS, SE=1) with cursor=3 (OTYPE_SENTRY_IE_FWD) as the
# sealing authority -- same mechanism already verified by
# cheriot_cseal_cunseal, just with a different otype value.
#
#   Test 1 (mstatus.MIE = 1 inside the callee -- IE_FWD sentry set it on entry)
#   Test 2 (ra holds a tagged capability inside the callee -- CJALR minted a
#           real backward sentry, not a plain integer return address)
#   Test 3 (mstatus.MIE = 0 after the return -- restored via the
#           auto-generated ID_BKWD sentry, since MIE was 0 at call time)
#   Test 4 (the callee actually executed -- marker check, guards against a
#           silently-skipped call)
#   Tests 5-6 (mcause = 0, mip = 0 -- no unexpected exception occurred)
#
# Verification: cosim (per-instruction Spike/RTL register compare) plus the
# self-check below (independent of cosim).
#
# Instruction encodings (opcode=0x5B for CHERIoT; CJALR itself is plain RISC-V
# JALR, opcode=0x67, no custom encoding needed):
#   cspecialr ca0, mtcc       = .word 0x03C0055B  (rd=a0, SCR=28=MTCC)
#   csetaddr  ca0,ca0,a1      = .word 0x20B5055B  (funct7=0x10, cs1=a0, rs2=a1, rd=a0)
#   cspecialr ca2, mscratchc  = .word 0x03E0065B  (rd=a2, SCR=30=MSCRATCHC)
#   csetaddr  ca2,ca2,a1      = .word 0x20B6065B  (funct7=0x10, cs1=a2, rs2=a1, rd=a2)
#   cseal     ca3,ca0,ca2     = .word 0x16C506DB  (funct7=0x0b, cs1=a0, rs2=a2, rd=a3)
#   cgettag   a0, cra         = .word 0xFE40855B  (rs2=0x04, rs1=ra=x1, rd=a0)
#   cmove     ct2, cra        = .word 0xFEA083DB  (rs2=0x0a, rs1=ra=x1, rd=t2)
#   cmove     cra, ct2        = .word 0xFEA380DB  (rs2=0x0a, rs1=t2=x7, rd=ra)

.globl main
main:
    csrci   mstatus, 8              # explicitly clear MIE -- known starting state = 0

    # jalr ra,... below overwrites ra with a sentry pointing back into this
    # test body; save crt's real return capability first (via CMove, which
    # preserves the tag -- a plain mv/addi would clear it) so every exit path
    # (success or fail) can restore it before its own ret, instead of
    # looping back into the CJALR call site forever.
    .word   0xFEA083DB               # cmove ct2, cra

    # a0 = MTCC with cursor moved to the call target (.Lcallee).
    .word   0x03C0055B              # cspecialr ca0, mtcc
    la      a1, .Lcallee
    .word   0x20B5055B              # csetaddr ca0, ca0, a1

    # a2 = MScratchC (sealing root, SE=1), cursor = 3 (OTYPE_SENTRY_IE_FWD:
    # forward sentry that sets mstatus.MIE on entry).
    .word   0x03E0065B              # cspecialr ca2, mscratchc
    li      a1, 3
    .word   0x20B6065B              # csetaddr ca2, ca2, a1

    # Seal the call target into a forward, interrupt-enable-on-entry sentry.
    .word   0x16C506DB              # cseal ca3, ca0, ca2

    li      t1, 0                   # marker: callee not yet reached
    jalr    ra, a3, 0               # CJALR call: rd=ra -> mints a backward
                                     # sentry in ra; cs1 otype=IE_FWD -> MIE<=1

    # ── returned from .Lcallee ────────────────────────────────────────────────
    # ── Test 3: mstatus.MIE restored to 0 (ra was sealed ID_BKWD, since MIE
    #    was 0 at the call above) ──────────────────────────────────────────────
    csrr    a0, mstatus
    andi    a0, a0, 8
    bnez    a0, .Lfail_test3

    # ── Test 4: callee actually executed (marker was set there) ─────────────
    li      a2, 1
    bne     t1, a2, .Lfail_test4

    j       .Lchecks_done

.Lcallee:
    # ── Test 1: mstatus.MIE = 1 here (IE_FWD sentry set it on entry) ────────
    csrr    a0, mstatus
    andi    a0, a0, 8
    beqz    a0, .Lfail_test1

    # ── Test 2: ra holds a tagged capability (real backward sentry) ─────────
    .word   0xFE40855B              # cgettag a0, cra
    beqz    a0, .Lfail_test2

    li      t1, 1                   # mark: callee executed
    jalr    x0, ra, 0               # CJALR return via the backward sentry:
                                     # unseals ra into PCC, restores MIE

.Lchecks_done:
    csrr    a0, mcause
    bne     a0, x0, .Lfail_test5
    csrr    a0, mip
    bne     a0, x0, .Lfail_test6

    li      a0, 0
    j       .Lexit

.Lfail_test1: li a0, 1; j .Lexit
.Lfail_test2: li a0, 2; j .Lexit
.Lfail_test3: li a0, 3; j .Lexit
.Lfail_test4: li a0, 4; j .Lexit
.Lfail_test5: li a0, 5; j .Lexit
.Lfail_test6: li a0, 6

.Lexit:
    .word   0xFEA380DB               # cmove cra, ct2  -- restore crt's real
                                      # return capability before returning.
    ret
