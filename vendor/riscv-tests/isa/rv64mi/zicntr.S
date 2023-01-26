# See LICENSE for license details.

#*****************************************************************************
# zicntr.S
#-----------------------------------------------------------------------------
#
# Test if Zicntr is implemented correctly
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  # Make sure reading the cycle counter in four ways doesn't trap.
  TEST_CASE( 2, x0, 0, csrrc  x0, cycle,    x0);
  TEST_CASE( 3, x0, 0, csrrs  x0, cycle,    x0);
  TEST_CASE( 4, x0, 0, csrrci x0, cycle,    0);
  TEST_CASE( 5, x0, 0, csrrsi x0, cycle,    0);
  TEST_CASE( 6, x0, 0, csrrc  x0, instret,  x0);
  TEST_CASE( 7, x0, 0, csrrs  x0, instret,  x0);
  TEST_CASE( 8, x0, 0, csrrci x0, instret,  0);
  TEST_CASE( 9, x0, 0, csrrsi x0, instret,  0);
#if __riscv_xlen == 32
  TEST_CASE(12, x0, 0, csrrc  x0, cycleh,   x0);
  TEST_CASE(13, x0, 0, csrrs  x0, cycleh,   x0);
  TEST_CASE(14, x0, 0, csrrci x0, cycleh,   0);
  TEST_CASE(15, x0, 0, csrrsi x0, cycleh,   0);
  TEST_CASE(16, x0, 0, csrrc  x0, instreth, x0);
  TEST_CASE(17, x0, 0, csrrs  x0, instreth, x0);
  TEST_CASE(18, x0, 0, csrrci x0, instreth, 0);
  TEST_CASE(19, x0, 0, csrrsi x0, instreth, 0);
#endif

2:
  TEST_PASSFAIL

  .align 2
  .global mtvec_handler
mtvec_handler:
  j fail

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
