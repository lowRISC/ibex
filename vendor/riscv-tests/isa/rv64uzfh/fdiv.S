# See LICENSE for license details.

#*****************************************************************************
# fdiv.S
#-----------------------------------------------------------------------------
#
# Test f{div|sqrt}.h instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64UF
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_FP_OP2_H(2,  fdiv.h, 1, 1.1557273520668288, 3.14159265, 2.71828182 );
  TEST_FP_OP2_H(3,  fdiv.h, 1,-0.9991093838555584,      -1234,     1235.1 );
  TEST_FP_OP2_H(4,  fdiv.h, 0,         3.14159265, 3.14159265,        1.0 );

  TEST_FP_OP1_H(5,  fsqrt.h, 1, 1.7724538498928541, 3.14159265 );
  TEST_FP_OP1_H(6,  fsqrt.h, 0,                100,      10000 );

  TEST_FP_OP1_H_DWORD_RESULT(7,  fsqrt.h, 0x10, 0x00007e00, -1.0 );

  TEST_FP_OP1_H(8,  fsqrt.h, 1, 13.076696, 171.0);


  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
