# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A single step ends while an execute trigger is set on the next address: debug
# mode must report cause STEP. Before and after, checks that the trigger fires
# on an address the program reaches, also as the first instruction of a step.
# The bench sends one halt request once the program waits for it.

#include "riscv_test.h"
#include "test_macros.h"

# dcsr.cause values (ibex_pkg::dbg_cause_e). encoding.h uses older names.
#define DBG_CAUSE_TRIGGER 2
#define DBG_CAUSE_HALTREQ 3
#define DBG_CAUSE_STEP    4

# The bench reads core status at +signature_addr, 4 bytes above SIGNATURE_ADDR.
#define CORE_STATUS_ADDR (SIGNATURE_ADDR + 4)

# phase (in .data) tracks the progress:
#   0 reset code running
#   1 waiting for the halt request
#   2 running to the trigger on hit
#   3 stepping over step_16
#   4 stepping onto the trigger on hit
#   5 done

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

  # Ask for the halt request and wait for it. Its handler resumes at
  # before_hit, so the loop never sees another phase.
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

  # Reached only from debug mode. The trigger stops the program at hit, and
  # the step stops it after step_16, so neither jump to fail is executed.
  .balign 4
before_hit:
  c.nop
hit:
  j    fail
step_16:
  c.nop
after_step:
  j    fail

done:
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 5
  bne  t0, t1, fail
  j    pass

  TEST_PASSFAIL

  # No exception is expected.
mtvec_handler:
  j    fail

debug_entry:
  csrw dscratch0, t0
  csrw dscratch1, t1
  la   t0, phase
  lw   t0, 0(t0)
  li   t1, 1
  beq  t0, t1, debug_halt
  li   t1, 2
  beq  t0, t1, debug_hit
  li   t1, 3
  beq  t0, t1, debug_step
  li   t1, 4
  beq  t0, t1, debug_step_hit
  j    fail

debug_halt:
  csrr t0, dcsr
  srli t0, t0, 6
  andi t0, t0, 7
  li   t1, DBG_CAUSE_HALTREQ
  bne  t0, t1, fail
  # Set an execute trigger on hit (write tdata1 last, as the debug spec says).
  csrwi tselect, 0
  csrw tdata1, zero
  la   t0, hit
  csrw tdata2, t0
  csrwi tdata1, 5
  la   t0, before_hit
  csrw dpc, t0
  li   t0, 2
  j    debug_set_phase

debug_hit:
  csrr t0, dcsr
  srli t0, t0, 6
  andi t0, t0, 7
  li   t1, DBG_CAUSE_TRIGGER
  bne  t0, t1, fail
  csrr t0, dpc
  la   t1, hit
  bne  t0, t1, fail
  # Move the trigger to the instruction after step_16 and step over it.
  csrw tdata1, zero
  la   t0, after_step
  csrw tdata2, t0
  csrwi tdata1, 5
  li   t0, DCSR_STEP
  csrs dcsr, t0
  la   t0, step_16
  csrw dpc, t0
  li   t0, 3
  j    debug_set_phase

debug_step:
  csrr t0, dcsr
  srli t0, t0, 6
  andi t0, t0, 7
  li   t1, DBG_CAUSE_STEP
  bne  t0, t1, fail
  csrr t0, dpc
  la   t1, after_step
  bne  t0, t1, fail
  # Keep stepping, but resume onto a trigger: it fires before hit executes.
  csrw tdata1, zero
  la   t0, hit
  csrw tdata2, t0
  csrwi tdata1, 5
  la   t0, hit
  csrw dpc, t0
  li   t0, 4
  j    debug_set_phase

debug_step_hit:
  csrr t0, dcsr
  srli t0, t0, 6
  andi t0, t0, 7
  li   t1, DBG_CAUSE_TRIGGER
  bne  t0, t1, fail
  csrr t0, dpc
  la   t1, hit
  bne  t0, t1, fail
  csrw tdata1, zero
  li   t0, DCSR_STEP
  csrc dcsr, t0
  la   t0, done
  csrw dpc, t0
  li   t0, 5

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
