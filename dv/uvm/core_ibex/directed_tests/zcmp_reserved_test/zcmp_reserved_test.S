# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Reserved Zcmp encodings must raise an illegal-instruction exception.
#
# Three reserved sub-spaces are exercised:
#  - cm.mvsa01 with r1s' == r2s' (both fields are destinations, so the eight
#    equal-register encodings are reserved);
#  - the cm.mv* group with funct2 = 00 or 10 (only 01 = cm.mvsa01 and
#    11 = cm.mva01s are defined);
#  - cm.push/cm.pop/cm.popretz/cm.popret with rlist 0..3.
# Each encoding must trap exactly once with mcause = 2 and mtval = the fetched
# 16-bit encoding, and must leave the state a real expansion would touch
# untouched: the move targets keep their values, a reserved register list
# leaves sp, ra, a0 and the words below sp alone. Legal neighbours of the
# sub-spaces are executed as controls.
#
# The encodings are emitted as raw halfwords because the pinned toolchain has
# no Zcmp support. The cosim check is relaxed for this test because the
# core_ibex cosim does not enable Zcmp for the reference model, so the model
# traps on every cm.* instruction. (If Zcmp is enabled there one day, note that
# the lowRISC riscv-isa-sim fork also executes the reserved cm.mvsa01 encodings
# unless its cm_mvsa01 gets a r1s' != r2s' check.)

#include "riscv_test.h"
#include "test_macros.h"

# Register use:
#   gp (TESTNUM) index of the check in progress, for the failure trace
#   s10          number of illegal-instruction traps taken
#   s11          mtval the trap handler expects on the next trap
#   t3, t4       scratch for the checks
#   t5, t6       scratch inside the trap handler

# cm.mvsa01 with r1s' == r2s' == \sreg. The encoding must trap once and must not
# write \sreg (the unfixed decoder expanded it into two writes to \sreg).
.macro CHECK_RESERVED_MVSA01 idx, encoding, sreg
  li   gp, \idx
  li   s11, \encoding
  li   a0, 0xa0a0a0a0
  li   a1, 0xa1a1a1a1
  li   \sreg, 0xc0ffee00 + \idx
  mv   t3, s10
  .2byte \encoding
  addi t3, t3, 1
  bne  t3, s10, fail
  li   t4, 0xc0ffee00 + \idx
  bne  t4, \sreg, fail
.endm

# cm.mv* with a reserved funct2. The encoding must trap once and must not
# write any of the registers the two defined moves use.
.macro CHECK_RESERVED_MV idx, encoding
  li   gp, \idx
  li   s11, \encoding
  li   a0, 0xa0a0a0a0
  li   a1, 0xa1a1a1a1
  li   s0, 0x50000000 + \idx
  li   s1, 0x51000000 + \idx
  mv   t3, s10
  .2byte \encoding
  addi t3, t3, 1
  bne  t3, s10, fail
  li   t4, 0xa0a0a0a0
  bne  t4, a0, fail
  li   t4, 0xa1a1a1a1
  bne  t4, a1, fail
  li   t4, 0x50000000 + \idx
  bne  t4, s0, fail
  li   t4, 0x51000000 + \idx
  bne  t4, s1, fail
.endm

# cm.push/cm.pop/cm.popretz/cm.popret with a reserved rlist. The encoding must
# trap once and must not adjust sp, store below sp, or write ra or a0 (the
# registers a real pop/popret/popretz of rlist 4 would load or clear).
.macro CHECK_RESERVED_RLIST idx, encoding
  li   gp, \idx
  li   s11, \encoding
  la   sp, stack_top
  li   ra, 0x1a000000 + \idx
  li   a0, 0xa0000000 + \idx
  li   t4, 0xdeadbeef
  sw   t4, -4(sp)
  sw   t4, -8(sp)
  sw   t4, -12(sp)
  sw   t4, -16(sp)
  mv   t3, s10
  .2byte \encoding
  addi t3, t3, 1
  bne  t3, s10, fail
  la   t4, stack_top
  bne  t4, sp, fail
  li   t4, 0x1a000000 + \idx
  bne  t4, ra, fail
  li   t4, 0xa0000000 + \idx
  bne  t4, a0, fail
  li   t3, 0xdeadbeef
  lw   t4, -4(sp)
  bne  t4, t3, fail
  lw   t4, -8(sp)
  bne  t4, t3, fail
  lw   t4, -12(sp)
  bne  t4, t3, fail
  lw   t4, -16(sp)
  bne  t4, t3, fail
.endm

RVTEST_RV32M
RVTEST_CODE_BEGIN

  li   s10, 0
  li   s11, 0

  # Reserved cm.mvsa01: 101 011 r1s' 01 r2s' 10 with r1s' == r2s' (s0..s7).
  CHECK_RESERVED_MVSA01  1, 0xac22, s0
  CHECK_RESERVED_MVSA01  2, 0xaca6, s1
  CHECK_RESERVED_MVSA01  3, 0xad2a, s2
  CHECK_RESERVED_MVSA01  4, 0xadae, s3
  CHECK_RESERVED_MVSA01  5, 0xae32, s4
  CHECK_RESERVED_MVSA01  6, 0xaeb6, s5
  CHECK_RESERVED_MVSA01  7, 0xaf3a, s6
  CHECK_RESERVED_MVSA01  8, 0xafbe, s7

  # Reserved funct2 of the cm.mv* group: 101 011 000 ff 001 10 with ff = 00, 10.
  CHECK_RESERVED_MV      9, 0xac06
  CHECK_RESERVED_MV     26, 0xac46

  # Reserved register lists: 101 11 fam 0 rlist spimm 10 with rlist 0..3
  # (fam = 00 push, 01 pop, 10 popretz, 11 popret), spimm = 0.
  CHECK_RESERVED_RLIST  10, 0xb802
  CHECK_RESERVED_RLIST  11, 0xb812
  CHECK_RESERVED_RLIST  12, 0xb822
  CHECK_RESERVED_RLIST  13, 0xb832
  CHECK_RESERVED_RLIST  14, 0xba02
  CHECK_RESERVED_RLIST  15, 0xba12
  CHECK_RESERVED_RLIST  16, 0xba22
  CHECK_RESERVED_RLIST  17, 0xba32
  CHECK_RESERVED_RLIST  18, 0xbc02
  CHECK_RESERVED_RLIST  19, 0xbc12
  CHECK_RESERVED_RLIST  20, 0xbc22
  CHECK_RESERVED_RLIST  21, 0xbc32
  CHECK_RESERVED_RLIST  22, 0xbe02
  CHECK_RESERVED_RLIST  23, 0xbe12
  CHECK_RESERVED_RLIST  24, 0xbe22
  CHECK_RESERVED_RLIST  25, 0xbe32

  # Controls: the legal neighbours must execute without trapping.
  # cm.mvsa01 s0, s1: s0 = a0, s1 = a1.
  li   gp, 30
  li   s11, 0
  li   a0, 0xa0a0a0a0
  li   a1, 0xa1a1a1a1
  li   s0, 0
  li   s1, 0
  mv   t3, s10
  .2byte 0xac26                 # cm.mvsa01 s0, s1
  bne  t3, s10, fail
  bne  s0, a0, fail
  bne  s1, a1, fail

  # cm.mva01s s2, s3: a0 = s2, a1 = s3.
  li   gp, 31
  li   s2, 0x52525252
  li   s3, 0x53535353
  li   a0, 0
  li   a1, 0
  mv   t3, s10
  .2byte 0xad6e                 # cm.mva01s s2, s3
  bne  t3, s10, fail
  bne  a0, s2, fail
  bne  a1, s3, fail

  # cm.push {ra}, -16 followed by cm.pop {ra}, 16: ra round-trips through the
  # stack and sp returns to where it started.
  li   gp, 32
  la   sp, stack_top
  li   ra, 0x5a5a5a5a
  mv   t3, s10
  .2byte 0xb842
  la   t4, stack_top
  addi t4, t4, -16
  bne  t4, sp, fail
  li   ra, 0
  .2byte 0xba42
  bne  t3, s10, fail
  la   t4, stack_top
  bne  t4, sp, fail
  li   t4, 0x5a5a5a5a
  bne  t4, ra, fail

  # 26 reserved encodings, 26 traps.
  li   gp, 33
  li   t3, 26
  bne  t3, s10, fail

  j    pass

  TEST_PASSFAIL

  # Every trap must be an illegal-instruction exception carrying the fetched
  # 16-bit encoding in mtval. Skip the halfword and resume.
  .balign 4
  .global mtvec_handler
mtvec_handler:
  csrr t5, mcause
  li   t6, CAUSE_ILLEGAL_INSTRUCTION
  bne  t5, t6, fail
  csrr t5, mtval
  bne  t5, s11, fail
  addi s10, s10, 1
  csrr t5, mepc
  addi t5, t5, 2
  csrw mepc, t5
  mret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
  .balign 16
stack_bot:
  .fill 16, 4, 0
stack_top:
  .fill 4, 4, 0
RVTEST_DATA_END
