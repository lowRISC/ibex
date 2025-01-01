# See LICENSE for license details.

#*****************************************************************************
# fclass.S
#-----------------------------------------------------------------------------
#
# Test fclass.h instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64UF
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  #define TEST_FCLASS_H(testnum, correct, input) \
    TEST_CASE(testnum, a0, correct, li a0, input; fmv.h.x fa0, a0; \
                                    fclass.h a0, fa0)

  TEST_FCLASS_H( 2, 1 << 0, 0xfc00 )
  TEST_FCLASS_H( 3, 1 << 1, 0xbc00 )
  TEST_FCLASS_H( 4, 1 << 2, 0x83ff )
  TEST_FCLASS_H( 5, 1 << 3, 0x8000 )
  TEST_FCLASS_H( 6, 1 << 4, 0x0000 )
  TEST_FCLASS_H( 7, 1 << 5, 0x03ff )
  TEST_FCLASS_H( 8, 1 << 6, 0x3c00 )
  TEST_FCLASS_H( 9, 1 << 7, 0x7c00 )
  TEST_FCLASS_H(10, 1 << 8, 0x7c01 )
  TEST_FCLASS_H(11, 1 << 9, 0x7e00 )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
