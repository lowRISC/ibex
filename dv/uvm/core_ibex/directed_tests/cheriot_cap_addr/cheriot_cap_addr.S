# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_cap_addr — CGetAddr on the three reset root capabilities
# =============================================================================
# Exercises CGetAddr (funct7=0x7F, rs2=0x0F), which returns the virtual address
# (cursor) of a capability.  This instruction is distinct from CGetBase (rs2=2)
# which returns the lower bound: CGetAddr = base + offset.
#
# At reset all three root SCRs have cursor = 0:
#   cheri_pkg.sv: all RESET_CAP structs initialise addr=0 and offset=0, so
#   rf_rdata_a (the integer address shadow of the cap register) = 0.
#
# The cheri_ex.sv implementation:
#   CFIELD_ADDR: result_data_o = rf_rdata_a;
# This simply returns the integer data word held alongside the capability.
#
#   Test 1 (MTCC address = 0)
#     MTCC cursor starts at the base of the address space.  A failure would
#     indicate that the integer address register initialisation is wrong, or
#     that CGetAddr is reading from the wrong pipeline source.
#
#   Test 2 (MTDC address = 0)
#     Same check for the memory data root.
#
#   Test 3 (MScratchC address = 0)
#     Confirms the seal root also starts with cursor=0.
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
#      cgetaddr writes to integer register a0, so its result is compared between
#      ibex and Spike on every step.  A mismatch in the address shadow register
#      immediately diverges → cosim FAIL.
#
#   2. Self-check (bne x0 against expected value 0):
#      If cgetaddr returns anything other than 0 the branch to .Lfail_testN is
#      taken and main() returns non-zero, which the UVM testbench marks FAILED.
#
# Inspired by clang_purecap_null.c __builtin_cheri_offset_get() and
# clang_purecap_capcmp.c offset/address checks (CTSRD/Cambridge).
# =============================================================================
#
# Note: CGetAddr uses rs2=0x0F (not 0x05) as decoded in ibex_decoder.sv:
#   5'h0f: CFIELD_ADDR
# Encoding for cgetaddr a0, ca0 (rd=x10, rs1=x10, rs2=0x0F):
#   funct7=0x7F, rs2=0b01111, rs1=0b01010, funct3=000, rd=0b01010
#   = 1111111_01111_01010_000_01010_1011011 = 0xFEF5055B
#
# Encodings:
#   cspecialr  ca0, mtcc      = .word 0x03C0055B
#   cspecialr  ca0, mtdc      = .word 0x03D0055B
#   cspecialr  ca0, mscratchc = .word 0x03E0055B
#   cgetaddr   a0,  ca0       = .word 0xFEF5055B  (funct7=0x7F, rs2=0x0F)
#
# Tests:
#   1. MTCC address = 0.
#   2. MTDC address = 0.
#   3. MScratchC address = 0.
#   4. mstatus.MIE still = 1 after the test body (no interrupt cleared it).
#   5. mcause = 0 (no exception or interrupt was recorded).
#   6. mip = 0 (no interrupt inputs are currently asserted).

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # ── Test 1: MTCC address = 0 ──────────────────────────────────────────────
    .word   0x03C0055B              # cspecialr ca0, mtcc
    .word   0xFEF5055B              # cgetaddr  a0,  ca0
    bne     a0, x0, .Lfail_test1

    # ── Test 2: MTDC address = 0 ──────────────────────────────────────────────
    .word   0x03D0055B              # cspecialr ca0, mtdc
    .word   0xFEF5055B              # cgetaddr  a0,  ca0
    bne     a0, x0, .Lfail_test2

    # ── Test 3: MScratchC address = 0 ─────────────────────────────────────────
    .word   0x03E0055B              # cspecialr ca0, mscratchc
    .word   0xFEF5055B              # cgetaddr  a0,  ca0
    bne     a0, x0, .Lfail_test3

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
