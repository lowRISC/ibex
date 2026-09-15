# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# =============================================================================
# Test: cheriot_pcc — Program Counter Capability (PCC) properties
# =============================================================================
# In CHERIoT-Ibex the Program Counter Capability (PCC) drives all instruction
# fetches.  AUIPCC (opcode=0x17, same encoding as RISC-V AUIPC) reads the PCC
# and adds (imm20 << 12) to the cursor.  With imm20=0, this gives the current
# PCC with cursor = address of the AUIPCC instruction itself.
#
# PCC_RESET_CAP in cheri_pkg.sv:
#   '{1'b1, RESETEXP, 33'h10000_0000, 0, OTYPE_UNSEALED, 12'h1eb, CPERMS_TX, 1'b0}
# This means: tag=1, same CPERMS_TX as MTCC (perms=0x1EB), full 32-bit range.
#
# ibex_decoder.sv decodes opcode 0x17 as CAUIPCC when CHERIoT is enabled.
# The result capability is written to rd (ca0 in this test).
#
#   Test 1 (PCC tag = 1)
#     The PCC must always be a valid (tagged) capability.  A tag=0 here
#     means the PCC reset cap initialisation is broken or CAUIPCC decoding
#     is writing the wrong data.
#
#   Test 2 (PCC has execute permission, EX bit 8 set)
#     The PCC is the execution root — it must have permit_execute.  Without
#     EX the processor could not legally fetch instructions through the PCC.
#     This confirms that PCC inherits CPERMS_TX (the execute class).
#
#   Test 3 (PCC has global permission, GL bit 0 set)
#     All CHERIoT root capabilities are global.  Confirms that the global
#     bit survives the PCC derivation path.
#
#   Tests 4-6 (interrupt state — no interrupt expected)
#     Machine-mode interrupts are enabled at the start of the test.
#     Test 4: mstatus.MIE still = 1.
#     Test 5: mcause = 0.
#     Test 6: mip = 0.
#
# Verification:
#   Two independent layers catch a faulty DUT:
#
#   1. Cosim (Spike vs ibex RTL, per instruction step):
#      cgettag and cgetperm write to integer register a0 → cosim verifies each
#      result against Spike's PCC model on every step.
#
#   2. Self-check (bne/beq + andi against expected bit values):
#      main() returns non-zero if any check fails → UVM testbench marks FAILED.
#
# Inspired by clang_purecap_capretaddr.c and clang_purecap_funptr.c which
# verify that function pointer capabilities are executable (CTSRD/Cambridge).
# AUIPCC provides a portable way to obtain the current PCC without needing
# a CHERIoT-aware compiler.
# =============================================================================
#
# Encoding:
#   auipcc ca0, 0 = 0x00000517
#     opcode=0x17 (AUIPCC/AUIPC), rd=x10=a0, imm20=0
#     In CHERIoT-Ibex: decoded as CAUIPCC, writes PCC with cursor=PC+0
#
# Tests:
#   1. PCC tag = 1 (it is a valid capability).
#   2. PCC permit_execute (bit 8) is set (it is an execute capability).
#   3. PCC global (bit 0) is set (it is a global capability).
#   4. mstatus.MIE = 1.
#   5. mcause = 0.
#   6. mip = 0.

.globl main
main:
    # Enable machine-mode interrupts for the duration of this test.
    csrsi   mstatus, 8              # set mstatus.MIE (bit 3)

    # Get the current PCC via AUIPCC (imm20=0 → cursor = address of this instr).
    .word   0x00000517              # auipcc ca0, 0

    # ── Test 1: PCC tag = 1 ───────────────────────────────────────────────────
    .word   0xFE45055B              # cgettag a0, ca0
    li      a1, 1
    bne     a0, a1, .Lfail_test1

    # ── Test 2: PCC has execute permission (bit 8) ────────────────────────────
    .word   0xFE05055B              # cgetperm a0, ca0
    andi    a1, a0, 0x100           # isolate EX (bit 8)
    beq     a1, x0, .Lfail_test2   # EX must be set

    # ── Test 3: PCC has global permission (bit 0) ─────────────────────────────
    andi    a1, a0, 0x1             # isolate GL (bit 0)
    beq     a1, x0, .Lfail_test3   # GL must be set

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
