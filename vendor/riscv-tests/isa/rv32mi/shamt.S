# See LICENSE for license details.

#*****************************************************************************
# shamt.S
#-----------------------------------------------------------------------------
#
# Test illegal shamt[5] of shift instruction in 32-bit ISA.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32M
RVTEST_CODE_BEGIN

  # Make sure slli with shamt[4] set is legal.
  TEST_CASE( 2, a0, 65536, li a0, 1; slli a0, a0, 16);

  # Make sure slli with shamt[5] set is not legal.
  TEST_CASE( 3, x0, 1, .word 0x02051513); # slli a0, a0, 32

  TEST_PASSFAIL

.align 2
.global mtvec_handler
mtvec_handler:
  # Trapping on test 3 is good.
  li t0, 3
  bne TESTNUM, t0, fail

  # Make sure CAUSE indicates an illegal instructino.
  csrr t0, mcause
  li t1, CAUSE_ILLEGAL_INSTRUCTION
  bne t0, t1, fail
  j pass

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
