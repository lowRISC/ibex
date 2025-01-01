# See LICENSE for license details.

#*****************************************************************************
# lw-unaligned.S
#-----------------------------------------------------------------------------
#
# Test that misaligned loads work or raise the correct exception
# This test assumes the target is little-endian
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  TEST_LD_OP( 2, lw, 0x04030201, 0,  tdat );
  TEST_LD_OP( 3, lw, 0x05040302, 1,  tdat );
  TEST_LD_OP( 4, lw, 0x06050403, 2,  tdat );
  TEST_LD_OP( 5, lw, 0x07060504, 3, tdat );

2:
  TEST_PASSFAIL

  .align 2
  .global mtvec_handler
mtvec_handler:
  MISALIGNED_LOAD_HANDLER

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
    .byte 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08

RVTEST_DATA_END
