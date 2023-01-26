# See LICENSE for license details.
#*****************************************************************************
# fcvt_w.S
#-----------------------------------------------------------------------------
#
# Test fcvt{wu|w|lu|l}.h instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64UF
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_FP_INT_OP_H( 2,  fcvt.w.h, 0x01,         -1,    -1.1, rtz);
  TEST_FP_INT_OP_H( 3,  fcvt.w.h, 0x00,         -1,    -1.0, rtz);
  TEST_FP_INT_OP_H( 4,  fcvt.w.h, 0x01,          0,    -0.9, rtz);
  TEST_FP_INT_OP_H( 5,  fcvt.w.h, 0x01,          0,     0.9, rtz);
  TEST_FP_INT_OP_H( 6,  fcvt.w.h, 0x00,          1,     1.0, rtz);
  TEST_FP_INT_OP_H( 7,  fcvt.w.h, 0x01,          1,     1.1, rtz);
  TEST_FP_INT_OP_H( 8,  fcvt.w.h, 0x00,      -2054, 0h:e803, rtz);
  TEST_FP_INT_OP_H( 9,  fcvt.w.h, 0x00,       2054, 0h:6803, rtz);

  TEST_FP_INT_OP_H(12, fcvt.wu.h, 0x10,          0,    -3.0, rtz);
  TEST_FP_INT_OP_H(13, fcvt.wu.h, 0x10,          0,    -1.0, rtz);
  TEST_FP_INT_OP_H(14, fcvt.wu.h, 0x01,          0,    -0.9, rtz);
  TEST_FP_INT_OP_H(15, fcvt.wu.h, 0x01,          0,     0.9, rtz);
  TEST_FP_INT_OP_H(16, fcvt.wu.h, 0x00,          1,     1.0, rtz);
  TEST_FP_INT_OP_H(17, fcvt.wu.h, 0x01,          1,     1.1, rtz);
  TEST_FP_INT_OP_H(18, fcvt.wu.h, 0x10,          0, 0h:e803, rtz);
  TEST_FP_INT_OP_H(19, fcvt.wu.h, 0x00,       2054, 0h:6803, rtz);

#if __riscv_xlen >= 64
  TEST_FP_INT_OP_H(22,  fcvt.l.h, 0x01,         -1,    -1.1, rtz);
  TEST_FP_INT_OP_H(23,  fcvt.l.h, 0x00,         -1,    -1.0, rtz);
  TEST_FP_INT_OP_H(24,  fcvt.l.h, 0x01,          0,    -0.9, rtz);
  TEST_FP_INT_OP_H(25,  fcvt.l.h, 0x01,          0,     0.9, rtz);
  TEST_FP_INT_OP_H(26,  fcvt.l.h, 0x00,          1,     1.0, rtz);
  TEST_FP_INT_OP_H(27,  fcvt.l.h, 0x01,          1,     1.1, rtz);

  TEST_FP_INT_OP_H(32, fcvt.lu.h, 0x10,          0,    -3.0, rtz);
  TEST_FP_INT_OP_H(33, fcvt.lu.h, 0x10,          0,    -1.0, rtz);
  TEST_FP_INT_OP_H(34, fcvt.lu.h, 0x01,          0,    -0.9, rtz);
  TEST_FP_INT_OP_H(35, fcvt.lu.h, 0x01,          0,     0.9, rtz);
  TEST_FP_INT_OP_H(36, fcvt.lu.h, 0x00,          1,     1.0, rtz);
  TEST_FP_INT_OP_H(37, fcvt.lu.h, 0x01,          1,     1.1, rtz);
  TEST_FP_INT_OP_H(38, fcvt.lu.h, 0x10,          0, 0h:e483, rtz);
#endif

  # test negative NaN, negative infinity conversion
  TEST_CASE( 42, x1, 0x000000007fffffff, la x1, tdat  ; flw f1,  0(x1); fcvt.w.h x1, f1)
  TEST_CASE( 43, x1, 0xffffffff80000000, la x1, tdat  ; flw f1,  8(x1); fcvt.w.h x1, f1)
#if __riscv_xlen >= 64
  TEST_CASE( 44, x1, 0x7fffffffffffffff, la x1, tdat  ; flw f1,  0(x1); fcvt.l.h x1, f1)
  TEST_CASE( 45, x1, 0x8000000000000000, la x1, tdat  ; flw f1,  8(x1); fcvt.l.h x1, f1)
#endif

  # test positive NaN, positive infinity conversion
  TEST_CASE( 52, x1, 0x000000007fffffff, la x1, tdat  ; flw f1,  4(x1); fcvt.w.h x1, f1)
  TEST_CASE( 53, x1, 0x000000007fffffff, la x1, tdat  ; flw f1, 12(x1); fcvt.w.h x1, f1)
#if __riscv_xlen >= 64
  TEST_CASE( 54, x1, 0x7fffffffffffffff, la x1, tdat  ; flw f1,  4(x1); fcvt.l.h x1, f1)
  TEST_CASE( 55, x1, 0x7fffffffffffffff, la x1, tdat  ; flw f1, 12(x1); fcvt.l.h x1, f1)
#endif

  # test NaN, infinity conversions to unsigned integer
  TEST_CASE( 62, x1, 0xffffffffffffffff, la x1, tdat  ; flw f1,  0(x1); fcvt.wu.h x1, f1)
  TEST_CASE( 63, x1, 0xffffffffffffffff, la x1, tdat  ; flw f1,  4(x1); fcvt.wu.h x1, f1)
  TEST_CASE( 64, x1,                  0, la x1, tdat  ; flw f1,  8(x1); fcvt.wu.h x1, f1)
  TEST_CASE( 65, x1, 0xffffffffffffffff, la x1, tdat  ; flw f1, 12(x1); fcvt.wu.h x1, f1)
#if __riscv_xlen >= 64
  TEST_CASE( 66, x1, 0xffffffffffffffff, la x1, tdat  ; flw f1,  0(x1); fcvt.lu.h x1, f1)
  TEST_CASE( 67, x1, 0xffffffffffffffff, la x1, tdat  ; flw f1,  4(x1); fcvt.lu.h x1, f1)
  TEST_CASE( 68, x1,                  0, la x1, tdat  ; flw f1,  8(x1); fcvt.lu.h x1, f1)
  TEST_CASE( 69, x1, 0xffffffffffffffff, la x1, tdat  ; flw f1, 12(x1); fcvt.lu.h x1, f1)
#endif
   
  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

# -NaN, NaN, -inf, +inf
#tdat:
#.word 0xffffffff
#.word 0x7fffffff
#.word 0xff800000
#.word 0x7f800000

tdat:
.word 0xffffffff
.word 0xffff7fff
.word 0xfffffc00
.word 0xffff7c00

RVTEST_DATA_END
