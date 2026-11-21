# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This test verifies that `mstatus.MPRV` is ignored in debug mode when
# `dcsr.mprven` is unset.

#include "riscv_test.h"
#include "test_macros.h"
#include "custom_macros.h"
#include "ibex_macros.h"

#define SET_PMP_NA4(addr, pmp_cfg, pmp_region) \
  la   t1, addr;                               \
  srli t1, t1, 2;                              \
  csrw pmpaddr##pmp_region, t1;                \
  SET_PMP_CFG(pmp_cfg, pmp_region)

#define DCSR_MPRVEN (1<<4)

# DmHaltAddr is the start of .text.init and DmExceptionAddr 8 bytes later.
# The reset code of RVTEST_CODE_BEGIN starts at offset 0x80.
  .section .text.init
  .option push
  .option norvc
  j    debug_entry
  nop
  j    debug_entry_exception
  .option pop

RVTEST_RV32M
RVTEST_CODE_BEGIN

  RESET_PMP

  # Setup PMP region for `pmp_protected_word` with an execute-only privilege
  # for the sake of resembling a real-world use case
  SET_PMP_NA4(pmp_protected_word, PMP_X | PMP_NA4, 0)

  # Set mstatus.MPRV=1 and MPP=U
  li    t0, MSTATUS_MPRV
  csrs  mstatus, t0
  li    t0, MSTATUS_MPP
  csrc  mstatus, t0

  # Default test result to 0 and trigger debug mode
  li    s1, 0
  wfi

  # Restore MPRV=0 so next memory access (RVTEST_FAIL/PASS) doesn't get blocked
  li    t0, MSTATUS_MPRV
  csrc  mstatus, t0

  bnez  s1, 1f
  RVTEST_FAIL
1:
  RVTEST_PASS

debug_entry:
  # The test relies on `dcsr.mprven` being `0`
  csrr  t0, dcsr
  andi  t0, t0, DCSR_MPRVEN
  bnez  t0, debug_entry_exception

  # Read `pmp_protected_word` (which should be accessible in M-mode)
  la    t0, pmp_protected_word
  lw    t1, 0(t0)
  li    s1, 1
  dret

debug_entry_exception:
  # PMP had denied access (debug mode incorrectly used U-mode privilege) or
  # the `dcsr.mprven` assumption does not hold.
  li    s1, 0
  dret

RVTEST_CODE_END

  .data
  .balign 4
pmp_protected_word:
  .word 0xA1A1A1A1

  .data
RVTEST_DATA_BEGIN
TEST_DATA
RVTEST_DATA_END
