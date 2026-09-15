# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cap_high — CGetHigh/CSetHigh round-trip
# =============================================================================
# CGetHigh (funct7=0x7f, rs2=0x17) returns the 32-bit "high" word of a
# capability's CHERIoT memory representation (ibex_cheriot_ex.sv:
# CFIELD_HIGH -> cheriot_cap_to_mem(cap), i.e. the packed base/top/exponent/
# otype/compressed-perms metadata used when a capability is (de)serialised to
# two 32-bit memory words). CSetHigh (funct7=0x16) is its counterpart:
# cd <-- cs1 (address/cursor only); cd's bounds/perms/otype <-- decode(rs2)
# via cheriot_mem_to_cap() (ibex_cheriot_ex.sv, CSET_HIGH case).
#
# Critically, cheriot_mem_to_cap() is called with the tag bit of BOTH its
# cap_mw and addr33 arguments forced to 0 (`{1'b0, rf_rdata_b}` /
# `{1'b0, rf_rdata_a}`), so `valid_in = cap_mw[32] & addr33[32]` is always 0:
# CSetHigh can NEVER produce a tagged (valid) capability, regardless of
# input. This is intentional -- constructing a capability's metadata from a
# raw integer word must never itself mint a valid capability. This test's
# main assertion is exactly that: metadata (perm/base/len/otype) round-trips
# correctly, cursor is taken from cs1, but the tag is always cleared.
#
#   Test 1 (tag = 0 after CSetHigh, always -- see above)
#   Test 2 (perm round-trips through CGetHigh/CSetHigh)
#   Test 3 (base round-trips)
#   Test 4 (len round-trips)
#   Test 5 (otype round-trips)
#   Test 6 (address = 0, taken from cs1's cursor, unaffected by the "high" word)
#   Tests 7-9 (interrupt state — no interrupt expected)
#
# Verification: cosim (per-instruction Spike/RTL register compare) plus the
# self-check below (independent of cosim).
#
# Instruction encodings (opcode=0x5B for CHERIoT):
#   cspecialr ca0, mtdc = .word 0x03D0055B  (rd=a0, SCR=29=MTDC)
#   cgetperm  t0, ca0   = .word 0xFE0502DB  (funct7=0x7f, rs2=0x00, rs1=a0, rd=t0)
#   cgetbase  t1, ca0   = .word 0xFE25035B  (rs2=0x02, rd=t1)
#   cgetlen   t2, ca0   = .word 0xFE3503DB  (rs2=0x03, rd=t2)
#   cgettype  s0, ca0   = .word 0xFE15045B  (rs2=0x01, rd=s0)
#   cgethigh  a1, ca0   = .word 0xFF7505DB  (rs2=0x17, rs1=a0, rd=a1)
#   csethigh  ca3,ca0,a1= .word 0x2CB506DB  (funct7=0x16, cs1=a0, rs2=a1, rd=a3)
#   cgettag   a4, ca3   = .word 0xFE46875B  (rs2=0x04, rs1=a3, rd=a4)
#   cgetperm  a4, ca3   = .word 0xFE06875B  (rs2=0x00)
#   cgetbase  a4, ca3   = .word 0xFE26875B  (rs2=0x02)
#   cgetlen   a4, ca3   = .word 0xFE36875B  (rs2=0x03)
#   cgettype  a4, ca3   = .word 0xFE16875B  (rs2=0x01)
#   cgetaddr  a4, ca3   = .word 0xFEF6875B  (rs2=0x0f)

.globl main
main:
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # a0 = MTDC (base=0, cursor=0, len=0xFFFFFFFF, perm=0x07F, type=0, tag=1)
    .word   0x03D0055B              # cspecialr ca0, mtdc

    # Save all metadata fields of a0 for later comparison.
    .word   0xFE0502DB              # cgetperm t0, ca0
    .word   0xFE25035B              # cgetbase t1, ca0
    .word   0xFE3503DB              # cgetlen  t2, ca0
    .word   0xFE15045B              # cgettype s0, ca0

    # Extract the packed "high" metadata word, then rebuild a capability from
    # it plus a0's cursor (0).
    .word   0xFF7505DB              # cgethigh a1, ca0
    .word   0x2CB506DB              # csethigh ca3, ca0, a1

    # ── Test 1: tag = 0 (CSetHigh can never mint a valid capability) ─────────
    .word   0xFE46875B              # cgettag a4, ca3
    bnez    a4, .Lfail_test1

    # ── Test 2: permissions round-trip through the "high" word ───────────────
    .word   0xFE06875B              # cgetperm a4, ca3
    bne     a4, t0, .Lfail_test2

    # ── Test 3: base round-trips ──────────────────────────────────────────────
    .word   0xFE26875B              # cgetbase a4, ca3
    bne     a4, t1, .Lfail_test3

    # ── Test 4: length round-trips ────────────────────────────────────────────
    .word   0xFE36875B              # cgetlen a4, ca3
    bne     a4, t2, .Lfail_test4

    # ── Test 5: otype round-trips ─────────────────────────────────────────────
    .word   0xFE16875B              # cgettype a4, ca3
    bne     a4, s0, .Lfail_test5

    # ── Test 6: address = 0 (taken from cs1's cursor, untouched by "high") ───
    .word   0xFEF6875B              # cgetaddr a4, ca3
    bnez    a4, .Lfail_test6

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
