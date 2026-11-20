# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Store to and load from the last word of the address space, which the
# testbench memory serves like any other address.

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  li   TESTNUM, 2
  la   t0, mtvec_handler
  csrw mtvec, t0

  li   t0, 0xfffffffc
  li   t1, 0x12345678
  sw   t1, 0(t0)
  lw   t2, 0(t0)
  bne  t1, t2, fail
  j    pass

  TEST_PASSFAIL

.balign 256
mtvec_handler:
  j    fail

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
