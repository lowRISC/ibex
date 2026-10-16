# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Store a halfword across the end of a read-only PMP region, then check that
# Ibex wrote the permitted high byte. The architecture allows this partial
# store but does not require it.

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  li   TESTNUM, 2
  la   t0, mtvec_handler
  csrw mtvec, t0

  # Locked read-only TOR region [ro_start, ro_end).
  la   t0, ro_start
  srli t1, t0, PMP_SHIFT
  csrw pmpaddr0, t1
  la   t0, ro_end
  srli t1, t0, PMP_SHIFT
  csrw pmpaddr1, t1
  li   t1, (PMP_L | PMP_TOR | PMP_R) << 8
  csrw pmpcfg0, t1

  li   t1, 0xa55a
  sh   t1, -1(t0)
  j    fail

store_faulted:
  lbu  t2, 0(t0)
  li   t3, 0xa5
  bne  t2, t3, fail
  j    pass

  TEST_PASSFAIL

.balign 256
mtvec_handler:
  csrr t3, mcause
  li   t4, CAUSE_STORE_ACCESS
  bne  t3, t4, fail
  la   t3, store_faulted
  csrw mepc, t3
  mret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

.balign 0x1000
ro_start: .zero 0x1000
ro_end:   .zero 0x1000
  TEST_DATA

RVTEST_DATA_END
