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

  TEST_LD_OP( 2, ld, 0x0807060504030201, 0, tdat );
  TEST_LD_OP( 3, ld, 0x0908070605040302, 1, tdat );
  TEST_LD_OP( 4, ld, 0x0a09080706050403, 2, tdat );
  TEST_LD_OP( 5, ld, 0x0b0a090807060504, 3, tdat );
  TEST_LD_OP( 6, ld, 0x0c0b0a0908070605, 4, tdat );
  TEST_LD_OP( 7, ld, 0x0d0c0b0a09080706, 5, tdat );
  TEST_LD_OP( 8, ld, 0x0e0d0c0b0a090807, 6, tdat );
  TEST_LD_OP( 9, ld, 0x0f0e0d0c0b0a0908, 7, tdat );

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
    .byte 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10

RVTEST_DATA_END
