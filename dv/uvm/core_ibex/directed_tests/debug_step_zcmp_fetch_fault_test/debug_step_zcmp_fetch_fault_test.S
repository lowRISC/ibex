# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Check step entry before the trap handler after a denied U-mode fetch.
# Exercise c.nop first, then cm.mva01s.

#include "riscv_test.h"
#include "test_macros.h"

# dcsr.cause values (ibex_pkg::dbg_cause_e). encoding.h uses older names.
#define DBG_CAUSE_HALTREQ 3
#define DBG_CAUSE_STEP    4

# The bench reads core status at +signature_addr, 4 bytes above SIGNATURE_ADDR.
#define CORE_STATUS_ADDR (SIGNATURE_ADDR + 4)

#define CSR_CPUCTRLSTS      0x7c0
#define CPUCTRLSTS_DUMMY_EN 0x4

# cm.mva01s s0, s7. The pinned toolchain has no Zcmp.
#define ENC_CM_MVA01S 0xac7e

# phase (in .data) tracks the progress:
#   0 reset code running
#   1 waiting for the halt request
#   2 stepping over nop_fault
#   3 stepping over mva_fault
#   4 done

# DmHaltAddr is the start of .text.init and DmExceptionAddr 8 bytes later. The
# reset code of RVTEST_CODE_BEGIN starts at offset 0x80.
  .section .text.init
  .option push
  .option norvc
  j    debug_entry
  nop
  j    fail
  .option pop

RVTEST_RV32M
RVTEST_CODE_BEGIN

  # Dummy instructions off, so nothing but the program enters ID.
  li   t0, CPUCTRLSTS_DUMMY_EN
  csrc CSR_CPUCTRLSTS, t0
  csrr t0, CSR_CPUCTRLSTS
  andi t0, t0, CPUCTRLSTS_DUMMY_EN
  bnez t0, fail

  # With no PMP region enabled, U mode can fetch nothing.
  csrw pmpcfg0, zero
  csrr t0, pmpcfg0
  bnez t0, fail

  # Ask for the halt request and wait for it. Its handler resumes at
  # nop_fault, so the loop never sees another phase.
  la   t0, phase
  li   t1, 1
  sw   t1, 0(t0)
  li   t0, CORE_STATUS_ADDR
  li   t1, (INITIALIZED << 8) | CORE_STATUS
  sw   t1, 0(t0)
  li   t2, 100000
1:
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 1
  bne  t0, t1, fail
  addi t2, t2, -1
  bnez t2, 1b
  j    fail

  # Reached only from debug mode, in U mode. Both fetches fault, so neither
  # jump to fail is executed.
  .balign 4
nop_fault:
  c.nop
  j    fail
mva_fault:
  .2byte ENC_CM_MVA01S
  j    fail

done:
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 4
  bne  t0, t1, fail
  j    pass

  TEST_PASSFAIL

  # Each step enters debug mode before the first instruction of the trap
  # handler, and the debug handler moves on.
mtvec_handler:
  j    fail

# Checks a step entry at the trap vector after the fetch of \insn faulted.
.macro check_step_fetch_fault insn
  csrr t0, dcsr
  srli t0, t0, 6
  andi t0, t0, 7
  li   t1, DBG_CAUSE_STEP
  bne  t0, t1, fail
  csrr t0, dpc
  la   t1, trap_vector
  bne  t0, t1, fail
  csrr t0, mcause
  li   t1, CAUSE_FETCH_ACCESS
  bne  t0, t1, fail
  la   t1, \insn
  csrr t0, mepc
  bne  t0, t1, fail
  csrr t0, mtval
  bne  t0, t1, fail
  # The trap handler runs in M mode.
  csrr t0, dcsr
  andi t0, t0, DCSR_PRV
  li   t1, PRV_M
  bne  t0, t1, fail
.endm

debug_entry:
  csrw dscratch0, t0
  csrw dscratch1, t1
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 1
  beq  t0, t1, debug_halt
  li   t1, 2
  beq  t0, t1, debug_step_nop
  li   t1, 3
  beq  t0, t1, debug_step_mva
  j    fail

debug_halt:
  csrr t0, dcsr
  srli t0, t0, 6
  andi t0, t0, 7
  li   t1, DBG_CAUSE_HALTREQ
  bne  t0, t1, fail
  # Step in U mode (dcsr.prv = PRV_U = 0).
  li   t0, DCSR_STEP
  csrs dcsr, t0
  li   t0, DCSR_PRV
  csrc dcsr, t0
  la   t0, nop_fault
  csrw dpc, t0
  li   t0, 2
  j    debug_set_phase

debug_step_nop:
  check_step_fetch_fault nop_fault
  li   t0, DCSR_PRV
  csrc dcsr, t0
  la   t0, mva_fault
  csrw dpc, t0
  li   t0, 3
  j    debug_set_phase

debug_step_mva:
  check_step_fetch_fault mva_fault
  li   t0, DCSR_STEP
  csrc dcsr, t0
  la   t0, done
  csrw dpc, t0
  li   t0, 4

debug_set_phase:
  la   t1, phase
  sw   t0, 0(t1)

debug_resume:
  csrr t0, dscratch0
  csrr t1, dscratch1
  dret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
phase:
  .word 0
RVTEST_DATA_END
