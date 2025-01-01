# See LICENSE for license details.

#*****************************************************************************
# ldst.S
#-----------------------------------------------------------------------------
#
# This test verifies that flw, fld, fsw, and fsd work properly.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32UF
RVTEST_CODE_BEGIN

  TEST_CASE(2, a0, 0xcafe4000, la a1, tdat; flh f1, 4(a1); fsh f1, 20(a1); lw a0, 20(a1))
  TEST_CASE(3, a0, 0xabadbf80, la a1, tdat; flh f1, 0(a1); fsh f1, 24(a1); lw a0, 24(a1))

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
.word 0xbf80bf80
.word 0x40004000
.word 0x40404040
.word 0xc080c080
.word 0xdeadbeef
.word 0xcafebabe
.word 0xabad1dea
.word 0x1337d00d

RVTEST_DATA_END
