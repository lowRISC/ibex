# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# FENCE.I after a store that rewrites the following instructions
# (lowRISC/ibex#2574).
#
# Each case stores a new encoding over an instruction and executes FENCE.I
# while that store (or a later load) may still be outstanding. The instruction
# executed after FENCE.I must be the new one. With a writeback stage and a data
# response that arrives after the refetch, the old encoding used to execute.
#
# The memory agent applies a store when it sees the request, so the old
# encoding cannot be fetched in this bench. The ID stage assertion
# IbexFenceINoFetchWithOutstandingMem flags the early refetch instead; the
# self-checks below catch it on a memory that performs the store on its
# response.

#include "riscv_test.h"
#include "test_macros.h"

#define CSR_CPUCTRLSTS        0x7c0
#define CPUCTRLSTS_ICACHE_EN  0x1

# addi a0, x0, imm
#define ADDI_A0(imm)          (((imm) << 20) | 0x513)

RVTEST_RV32M
RVTEST_CODE_BEGIN

  # Run with the instruction cache on where there is one. Without one the bit
  # reads as zero and has no effect.
  csrsi CSR_CPUCTRLSTS, CPUCTRLSTS_ICACHE_EN

  .option push
  .option norvc

  # 1: word store directly before FENCE.I.
  li    TESTNUM, 1
  la    a1, target_sw
  li    t1, ADDI_A0(7)
  sw    t1, 0(a1)
  fence.i
target_sw:
  addi  a0, x0, 1
  li    t2, 7
  bne   a0, t2, fail

  # 2: halfword store over the upper half (the immediate) of the instruction.
  li    TESTNUM, 2
  la    a1, target_sh
  li    t1, (ADDI_A0(9) >> 16)
  sh    t1, 2(a1)
  fence.i
target_sh:
  addi  a0, x0, 1
  li    t2, 9
  bne   a0, t2, fail

  # 3: the store is followed by a load, which is the access outstanding when
  # FENCE.I arrives.
  li    TESTNUM, 3
  la    a1, target_ld
  li    t1, ADDI_A0(5)
  sw    t1, 0(a1)
  lw    t3, 0(a1)
  fence.i
target_ld:
  addi  a0, x0, 1
  li    t2, 5
  bne   a0, t2, fail
  bne   t3, t1, fail

  # 4: rewrite the same instruction many times, so each FENCE.I sees a
  # different data response delay. The old encoding holds the previous count.
  li    TESTNUM, 4
  la    a1, target_loop
  li    t0, 1
  li    t4, 33
1:
  slli  t1, t0, 20
  ori   t1, t1, 0x513
  sw    t1, 0(a1)
  fence.i
target_loop:
  addi  a0, x0, 0
  bne   a0, t0, fail
  addi  t0, t0, 1
  bne   t0, t4, 1b

  # 5: rewrite a function that was executed (and cached) before.
  li    TESTNUM, 5
  jal   patch_fn
  li    t2, 1
  bne   a0, t2, fail
  la    a1, patch_fn
  li    t1, ADDI_A0(11)
  sw    t1, 0(a1)
  fence.i
  jal   patch_fn
  li    t2, 11
  bne   a0, t2, fail

  j     pass

  .balign 64
patch_fn:
  addi  a0, x0, 1
  ret

  .option pop

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
