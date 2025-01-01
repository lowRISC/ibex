# See LICENSE for license details.

#*****************************************************************************
# fadd.S
#-----------------------------------------------------------------------------
#
# Test f{add|sub|mul}.h instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64UF
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_FP_OP2_H( 2,  fadd.h, 0,                3.5,        2.5,        1.0 );
  TEST_FP_OP2_H( 3,  fadd.h, 1,              -1234,    -1235.1,        1.1 );
  TEST_FP_OP2_H( 4,  fadd.h, 1,                3.14,       3.13,      0.01 );

  TEST_FP_OP2_H( 5,  fsub.h, 0,                1.5,        2.5,        1.0 );
  TEST_FP_OP2_H( 6,  fsub.h, 1,              -1234,    -1235.1,       -1.1 );
  TEST_FP_OP2_H( 7,  fsub.h, 1,              3.14,        3.15,       0.01 );

  TEST_FP_OP2_H( 8,  fmul.h, 0,                2.5,        2.5,        1.0 );
  TEST_FP_OP2_H( 9,  fmul.h, 0,             1235.1,    -1235.1,       -1.0 );
  TEST_FP_OP2_H(10,  fmul.h, 1,                 1.1,      11.0,        0.1 );

  # Is the canonical NaN generated for Inf - Inf?
  TEST_FP_OP2_H(11,  fsub.h, 0x10, qNaNh, Inf, Inf);

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
