#*****************************************************************************
#-----------------------------------------------------------------------------
#
# Test CBO.ZERO instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  la  x1, tdat
  .word 0x0040A00F  # cbo.zero(x1)
  TEST_LD_OP( 1, ld, 0, 0,  tdat )
  TEST_LD_OP( 2, ld, 0, 8,  tdat )
  TEST_LD_OP( 3, ld, 0, 16, tdat )
  TEST_LD_OP( 4, ld, 0, 24, tdat )
  TEST_LD_OP( 5, ld, 0, 32, tdat )
  TEST_LD_OP( 6, ld, 0, 40, tdat )
  TEST_LD_OP( 7, ld, 0, 48, tdat )
  TEST_LD_OP( 8, ld, 0, 56, tdat )

  j pass

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:  .dword 0xdeadbeefdeadbeef

RVTEST_DATA_END
