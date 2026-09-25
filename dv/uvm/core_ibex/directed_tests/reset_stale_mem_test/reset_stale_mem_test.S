# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Store a marker outside the binary and request a reset through mscratch.
# After the reboot, fail if that word still contains the marker.

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32M
RVTEST_CODE_BEGIN

  li   TESTNUM, 2
  la   t0, _end
  addi t0, t0, 0x100
  li   t2, 0x5a5a5a5a
  lw   t1, 0(t0)
  beq  t1, t2, fail
  sw   t2, 0(t0)
  csrw mscratch, x0

  # Keep running until the testbench has reset the core.
  li   t3, 2000
1:
  addi t3, t3, -1
  bnez t3, 1b
  j    pass

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
