# See LICENSE for license details.

#*****************************************************************************
# structural.S
#-----------------------------------------------------------------------------
#
# This test verifies that the FPU correctly obviates structural hazards on its
# writeback port (e.g. fadd followed by fsgnj)
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64UF
RVTEST_CODE_BEGIN

li x12, 1

li x2, 0x3FF0000000000000
li x1, 0x3F800000

#define TEST(testnum, nops)     \
test_ ## testnum: \
  li  TESTNUM, testnum; \
  fmv.d.x  f4, x0    ;\
  fmv.s.x  f3, x0    ;\
  fmv.d.x  f2, x2    ;\
  fmv.s.x  f1, x1    ;\
  j 1f ;\
  .align 5        ;\
1:fmul.d  f4, f2, f2  ;\
  nops          ;\
  fsgnj.s f3, f1, f1 ;\
  fmv.x.d  x4, f4    ;\
  fmv.x.s  x5, f3    ;\
  beq     x1, x5, 2f  ;\
  j fail;\
2:beq     x2, x4, 2f  ;\
  j fail; \
2:fmv.d.x  f2, zero    ;\
  fmv.s.x  f1, zero    ;\

TEST(1,;)
TEST(2,nop)
TEST(3,nop;nop)
TEST(4,nop;nop;nop)
TEST(5,nop;nop;nop;nop)
TEST(6,nop;nop;nop;nop;nop)
TEST(7,nop;nop;nop;nop;nop;nop)

TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
