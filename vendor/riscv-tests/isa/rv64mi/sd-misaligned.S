# See LICENSE for license details.

#*****************************************************************************
# sd-unaligned.S
#-----------------------------------------------------------------------------
#
# Test that misaligned stores work or raise the correct exception
# This test assumes the target is little-endian
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  TEST_ST_OP( 2, ld, sd, 0x0102030405060708, 0, tdat );
  TEST_ST_OP( 3, ld, sd, 0x090a0b0c0d0e0f10, 1, tdat );
  TEST_ST_OP( 4, ld, sd, 0x1112131415161718, 2, tdat );
  TEST_ST_OP( 5, ld, sd, 0x191a1b1c1d1e1f20, 3, tdat );
  TEST_ST_OP( 6, ld, sd, 0x2122232425262728, 4, tdat );
  TEST_ST_OP( 7, ld, sd, 0x292a2b2c2d2e2f30, 5, tdat );
  TEST_ST_OP( 8, ld, sd, 0x3132333435363738, 6, tdat );
  TEST_ST_OP( 9, ld, sd, 0x393a3b3c3d3e3f40, 7, tdat );

2:
  TEST_PASSFAIL

  .align 2
  .global mtvec_handler
mtvec_handler:
  MISALIGNED_STORE_HANDLER

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
    .zero 16

RVTEST_DATA_END
