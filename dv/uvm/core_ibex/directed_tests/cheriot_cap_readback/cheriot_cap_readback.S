# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cap_readback — Field-by-field CSC→CLC round-trip
# =============================================================================
# Extends cheriot_rtos_clc_csc by comparing ALL capability metadata fields
# (not only the tag bit) before and after a CSC→CLC round-trip.
#
# Self-checking: returns 0 on success, a distinct non-zero code on each
# field mismatch.  Does NOT rely on the Sail cosim step oracle to determine
# pass/fail — the assembly self-check is independent of the cosim.
#
# ── Round-trip 1: MTDC (full-range unsealed data capability) ──────────────
#   Expects after CLC: tag=1, perm=0x07F, base=0, len=0xFFFFFFFF, addr=0,
#   type=0 (OTYPE_UNSEALED).  Then SW revokes: reload → tag=0.
#
# ── Round-trip 2: MTCC (execute root capability) ──────────────────────────
#   Expects after CLC: all fields identical to pre-store snapshot.
#   MTCC perms=0x1EB (EX bit set), base=0, len=0xFFFFFFFF, addr=0, type=0.
#   Then SW revokes: reload → tag=0.
#
# Memory: capabilities stored at 0x80080000 (8-byte-aligned data address,
#         well above the instruction range ending at 0x8003FFFF).
#
# Instruction encodings (opcode=0x5B for CHERIoT, funct7=0x7F for CGet*):
#
#   cspecialr a0, mtdc  = .word 0x03D0055B  (rd=a0, SCR=29=MTDC)
#   cspecialr a2, mtdc  = .word 0x03D0065B  (rd=a2, SCR=29=MTDC)
#   cspecialr a2, mtcc  = .word 0x03C0065B  (rd=a2, SCR=28=MTCC)
#   csetaddr  a0,a0,a1  = .word 0x20B5055B  (funct7=0x10, rd=a0, cs1=a0, rs2=a1)
#   sc a2, 0(a0)        = .word 0x00C53023  (STORE funct3=011: CSC)
#   lc a3, 0(a0)        = .word 0x00053683  (LOAD  funct3=011: CLC)
#
#   CGet* from a2 (rs1=01100) into t0-t2/s0-s1:
#     cgetperm t0, a2   = .word 0xFE0602DB  (rs2=0x00, rd=t0=x5)
#     cgetbase t1, a2   = .word 0xFE26035B  (rs2=0x02, rd=t1=x6)
#     cgetlen  t2, a2   = .word 0xFE3603DB  (rs2=0x03, rd=t2=x7)
#     cgetaddr s0, a2   = .word 0xFEF6045B  (rs2=0x0F, rd=s0=x8)
#     cgettype s1, a2   = .word 0xFE1604DB  (rs2=0x01, rd=s1=x9)
#
#   NOTE: destinations must stay within x0-x15 -- CHERIoT's 16-register
#   limit makes any access to x16+ (e.g. t3=x28, t4=x29) illegal under
#   cheriot_enable_i (ibex_decoder.sv's illegal_reg_16 check). The original
#   ibex-private version of this test used t3/t4; ported here to s0/s1.
#
#   CGet* from a3 (rs1=01101) into a5:
#     cgettag  a5, a3   = .word 0xFE4687DB  (rs2=0x04, rd=a5=x15)
#     cgetperm a5, a3   = .word 0xFE0687DB  (rs2=0x00)
#     cgetbase a5, a3   = .word 0xFE2687DB  (rs2=0x02)
#     cgetlen  a5, a3   = .word 0xFE3687DB  (rs2=0x03)
#     cgetaddr a5, a3   = .word 0xFEF687DB  (rs2=0x0F)
#     cgettype a5, a3   = .word 0xFE1687DB  (rs2=0x01)
#
# Return codes:
#   0   = PASS
#   1-7 = MTDC round-trip failure (tag/perm/base/len/addr/type/revoke)
#   8-14= MTCC round-trip failure (tag/perm/base/len/addr/type/revoke)
#   15  = unexpected: mstatus.MIE cleared
#   16  = unexpected: mcause non-zero (exception during test)
#   17  = unexpected: mip non-zero
# =============================================================================

.globl main
main:
    csrsi   mstatus, 8              # set MIE; cleared by any unexpected exception

    # ── Round-trip 1: MTDC ──────────────────────────────────────────────────

    # a2 = MTDC (the capability we will store and load back)
    .word   0x03D0065B              # cspecialr a2, mtdc

    # Save all metadata fields of a2 into caller-saved temporaries.
    # These survive the CSC/CLC sequence (no CHERIoT instr writes t0-t2/s0-s1).
    .word   0xFE0602DB              # cgetperm  t0, a2   → t0 = permissions
    .word   0xFE26035B              # cgetbase  t1, a2   → t1 = base address
    .word   0xFE3603DB              # cgetlen   t2, a2   → t2 = length (0xFFFFFFFF for full-range)
    .word   0xFEF6045B              # cgetaddr  s0, a2   → s0 = cursor (0 at reset)
    .word   0xFE1604DB              # cgettype  s1, a2   → s1 = otype (0 = OTYPE_UNSEALED)

    # a0 = MTDC with cursor set to 0x80080000 (authority for CSC/CLC)
    .word   0x03D0055B              # cspecialr a0, mtdc
    lui     a1, 0x80080             # a1 = 0x80080000
    .word   0x20B5055B              # csetaddr  a0, a0, a1

    # CSC a2 to 0x80080000; CLC back into a3
    .word   0x00C53023              # sc a2, 0(a0)   — CSC
    .word   0x00053683              # lc a3, 0(a0)   — CLC

    # Check tag == 1
    .word   0xFE4687DB              # cgettag   a5, a3
    li      a4, 1
    bne     a5, a4, .Lfail1_tag

    # Check permissions preserved
    .word   0xFE0687DB              # cgetperm  a5, a3
    bne     a5, t0, .Lfail1_perm

    # Check base preserved
    .word   0xFE2687DB              # cgetbase  a5, a3
    bne     a5, t1, .Lfail1_base

    # Check length preserved
    .word   0xFE3687DB              # cgetlen   a5, a3
    bne     a5, t2, .Lfail1_len

    # Check cursor (address) preserved
    .word   0xFEF687DB              # cgetaddr  a5, a3
    bne     a5, s0, .Lfail1_addr

    # Check otype preserved
    .word   0xFE1687DB              # cgettype  a5, a3
    bne     a5, s1, .Lfail1_type

    # Revocation: integer store to same slot clears capability tag
    sw      x0, 0(a0)
    .word   0x00053683              # lc a3, 0(a0)
    .word   0xFE4687DB              # cgettag a5, a3
    bnez    a5, .Lfail1_revoke

    # ── Round-trip 2: MTCC ──────────────────────────────────────────────────

    # a2 = MTCC (execute root: perms=0x1EB, base=0, len=0xFFFFFFFF, addr=0)
    .word   0x03C0065B              # cspecialr a2, mtcc

    # Save all metadata fields of a2
    .word   0xFE0602DB              # cgetperm  t0, a2
    .word   0xFE26035B              # cgetbase  t1, a2
    .word   0xFE3603DB              # cgetlen   t2, a2
    .word   0xFEF6045B              # cgetaddr  s0, a2
    .word   0xFE1604DB              # cgettype  s1, a2

    # a0 still holds MTDC with cursor=0x80080000; reuse as authority.
    # (The SW above wrote only to memory; a0's capability tag is intact.)
    .word   0x00C53023              # sc a2, 0(a0)   — CSC MTCC to 0x80080000
    .word   0x00053683              # lc a3, 0(a0)   — CLC back into a3

    # Check tag == 1
    .word   0xFE4687DB              # cgettag   a5, a3
    li      a4, 1
    bne     a5, a4, .Lfail2_tag

    # Check permissions preserved
    .word   0xFE0687DB              # cgetperm  a5, a3
    bne     a5, t0, .Lfail2_perm

    # Check base preserved
    .word   0xFE2687DB              # cgetbase  a5, a3
    bne     a5, t1, .Lfail2_base

    # Check length preserved
    .word   0xFE3687DB              # cgetlen   a5, a3
    bne     a5, t2, .Lfail2_len

    # Check cursor preserved
    .word   0xFEF687DB              # cgetaddr  a5, a3
    bne     a5, s0, .Lfail2_addr

    # Check otype preserved
    .word   0xFE1687DB              # cgettype  a5, a3
    bne     a5, s1, .Lfail2_type

    # Revocation
    sw      x0, 0(a0)
    .word   0x00053683              # lc a3, 0(a0)
    .word   0xFE4687DB              # cgettag a5, a3
    bnez    a5, .Lfail2_revoke

    # ── Interrupt-state sanity check ────────────────────────────────────────
    # Any CHERIoT exception would have cleared MIE (mstatus.bit3) and set
    # mcause.  A non-zero result here means an unexpected exception fired.
    csrr    a0, mstatus
    andi    a1, a0, 8
    beq     a1, x0, .Lfail_mie
    csrr    a0, mcause
    bne     a0, x0, .Lfail_mcause
    csrr    a0, mip
    bne     a0, x0, .Lfail_mip

    li      a0, 0
    ret

.Lfail1_tag:    li a0,  1; ret
.Lfail1_perm:   li a0,  2; ret
.Lfail1_base:   li a0,  3; ret
.Lfail1_len:    li a0,  4; ret
.Lfail1_addr:   li a0,  5; ret
.Lfail1_type:   li a0,  6; ret
.Lfail1_revoke: li a0,  7; ret
.Lfail2_tag:    li a0,  8; ret
.Lfail2_perm:   li a0,  9; ret
.Lfail2_base:   li a0, 10; ret
.Lfail2_len:    li a0, 11; ret
.Lfail2_addr:   li a0, 12; ret
.Lfail2_type:   li a0, 13; ret
.Lfail2_revoke: li a0, 14; ret
.Lfail_mie:     li a0, 15; ret
.Lfail_mcause:  li a0, 16; ret
.Lfail_mip:     li a0, 17; ret
