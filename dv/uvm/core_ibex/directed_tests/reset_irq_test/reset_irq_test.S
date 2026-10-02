# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Enable every interrupt, write mscratch, then wait for an interrupt. The
# testbench resets the core at the first write and raises one interrupt after
# the second, so only the rebooted program leaves the loop.

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32M
RVTEST_CODE_BEGIN

  li   TESTNUM, 2
  la   t0, vector_table
  csrw mtvec, t0
  li   s0, 0
  li   t0, -1
  csrw mie, t0
  csrsi mstatus, MSTATUS_MIE
  csrw mscratch, x0

1:
  beqz s0, 1b
  j    pass

  TEST_PASSFAIL

# Ibex takes interrupts in vectored mode: exceptions use entry 0, interrupt N
# uses entry N.
.balign 256
.option push
.option norvc
vector_table:
  j    fail
  .rept 31
  j    irq_handler
  .endr
.option pop

irq_handler:
  li   s0, 1
  # Return with interrupts disabled, as the line stays high until the
  # testbench drops it.
  li   t0, MSTATUS_MPIE
  csrc mstatus, t0
  csrw mscratch, x0
  mret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
