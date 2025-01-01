# See LICENSE for license details.

#*****************************************************************************
# sw-unaligned.S
#-----------------------------------------------------------------------------
#
# Test that misaligned stores work or raise the correct exception
# This test assumes the target is little-endian
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  TEST_ST_OP( 2, lw, sw, 0x12345678, 0, tdat );
  TEST_ST_OP( 3, lw, sw, 0xffffffff9abcdef0, 1, tdat );
  TEST_ST_OP( 4, lw, sw, 0xffffffffdeadbeef, 2, tdat );
  TEST_ST_OP( 5, lw, sw, 0xfffffffffeed0011, 3, tdat );

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
    .zero 8

RVTEST_DATA_END
