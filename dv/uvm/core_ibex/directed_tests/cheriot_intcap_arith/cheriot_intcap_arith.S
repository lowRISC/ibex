# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_intcap_arith — integer arithmetic clears capability tag
# =============================================================================
# In CHERIoT-Ibex, any instruction that writes an integer result to a register
# (as opposed to a capability result) clears the capability tag of that register.
# This test exercises a broad set of integer ALU operations and verifies that
# each one produces a result with tag = 0.
#
# This property underlies the safety guarantee of the CHERI model: you cannot
# forge a capability by doing arithmetic on integers — the only way to obtain
# a tagged capability is through capability-producing instructions (CSpecialR,
# CSetBounds, etc.).
#
#   Tests 1-8 (integer ALU → tag = 0)
#     Test 1: addi (li a0, 42 → addi a0, x0, 42): basic integer load
#     Test 2: add  (add a0, a0, a1): register-register addition
#     Test 3: sub  (sub a0, a0, a1): register-register subtraction
#     Test 4: andi (andi a0, a0, 0xFF): immediate AND
#     Test 5: ori  (ori a0, x0, 0x7F): immediate OR
#     Test 6: xori (xori a0, a0, -1): bitwise NOT via XOR with -1
#     Test 7: slli (slli a0, a0, 3): logical shift left
#     Test 8: mul  (mul a0, a0, a1): multiply (rv32m extension)
#     Each sub-test: perform the operation, then cgettag a0, ca0 → 0.
#
#   Tests 9-11 (interrupt state — no interrupt expected)
#     Machine-mode interrupts are enabled at the start of the test.
#     Test 9:  mstatus.MIE still = 1.
#     Test 10: mcause = 0.
#     Test 11: mip = 0.
#
# Verification:
#   Two independent layers catch a faulty DUT:
#
#   1. Cosim (Spike vs ibex RTL, per instruction step):
#      cgettag writes to integer register a0, so its result is compared between
#      ibex and Spike on every step.  If the RTL fails to clear the tag when an
#      integer instruction writes a register, Spike returns 0 but the DUT returns
#      1 → cosim FAIL.
#
#   2. Self-check (bne against expected value 0):
#      If any cgettag returns non-zero, the branch to .Lfail_testN is taken and
#      main() returns a non-zero error code → UVM testbench marks FAILED.
#
# Inspired by clang_purecap_intcap.c (integer-to-capability casts produce
# untagged results) and clang_purecap_intcapmath.c/uintcapmath.c (arithmetic
# on __intcap_t values — CTSRD/Cambridge).
# =============================================================================
#
# Note: cgettag a0, ca0 is .word 0xFE45055B (funct7=0x7F, rs2=4).
# All inputs are created via integer operations (li, which expands to addi
# x0, imm), so they start with tag=0 and all subsequent integer ops preserve 0.
#
# Tests:
#    1. li (addi with x0): basic integer immediate load.
#    2. add (register + register).
#    3. sub (register - register).
#    4. andi (register AND immediate).
#    5. ori (x0 OR immediate).
#    6. xori (XOR with -1 = bitwise NOT).
#    7. slli (logical left shift).
#    8. mul (rv32m multiply).
#    9. mstatus.MIE still = 1.
#   10. mcause = 0.
#   11. mip = 0.

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # ── Test 1: li (addi x0, imm) → tag = 0 ──────────────────────────────────
    li      a0, 42
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test1

    # ── Test 2: add → tag = 0 ─────────────────────────────────────────────────
    li      a0, 100
    li      a1, 200
    add     a0, a0, a1
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test2

    # ── Test 3: sub → tag = 0 ─────────────────────────────────────────────────
    li      a0, 500
    li      a1, 200
    sub     a0, a0, a1
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test3

    # ── Test 4: andi → tag = 0 ────────────────────────────────────────────────
    li      a0, 0xABC
    andi    a0, a0, 0xFF
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test4

    # ── Test 5: ori (from x0) → tag = 0 ──────────────────────────────────────
    ori     a0, x0, 0x7F
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test5

    # ── Test 6: xori with -1 (bitwise NOT) → tag = 0 ─────────────────────────
    li      a0, 0x5A5A5A5A
    xori    a0, a0, -1
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test6

    # ── Test 7: slli → tag = 0 ────────────────────────────────────────────────
    li      a0, 1
    slli    a0, a0, 10
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test7

    # ── Test 8: mul → tag = 0 ─────────────────────────────────────────────────
    li      a0, 7
    li      a1, 11
    mul     a0, a0, a1
    .word   0xFE45055B              # cgettag a0, ca0
    bne     a0, x0, .Lfail_test8

    # ── Interrupt state verification (no interrupt expected) ──────────────────
    csrr    a0, mstatus
    andi    a1, a0, 8
    beq     a1, x0, .Lfail_test9
    csrr    a0, mcause
    bne     a0, x0, .Lfail_test10
    csrr    a0, mip
    bne     a0, x0, .Lfail_test11

    li      a0, 0
    ret

.Lfail_test1:  li a0, 1;  ret
.Lfail_test2:  li a0, 2;  ret
.Lfail_test3:  li a0, 3;  ret
.Lfail_test4:  li a0, 4;  ret
.Lfail_test5:  li a0, 5;  ret
.Lfail_test6:  li a0, 6;  ret
.Lfail_test7:  li a0, 7;  ret
.Lfail_test8:  li a0, 8;  ret
.Lfail_test9:  li a0, 9;  ret
.Lfail_test10: li a0, 10; ret
.Lfail_test11: li a0, 11; ret
