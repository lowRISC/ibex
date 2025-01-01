# See LICENSE for license details.

#*****************************************************************************
# fmadd.S
#-----------------------------------------------------------------------------
#
# Test f[n]m{add|sub}.h and f[n]m{add|sub}.h instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64UF
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_FP_OP3_H( 2,  fmadd.h, 0,                 3.5,  1.0,        2.5,        1.0 );
  TEST_FP_OP3_H( 3,  fmadd.h, 1,                13.2, -1.0,      -12.1,        1.1 );
  TEST_FP_OP3_H( 4,  fmadd.h, 0,               -12.0,  2.0,       -5.0,       -2.0 );

  TEST_FP_OP3_H( 5, fnmadd.h, 0,                -3.5,  1.0,        2.5,        1.0 );
  TEST_FP_OP3_H( 6, fnmadd.h, 1,               -13.2, -1.0,      -12.1,        1.1 );
  TEST_FP_OP3_H( 7, fnmadd.h, 0,                12.0,  2.0,       -5.0,       -2.0 );

  TEST_FP_OP3_H( 8,  fmsub.h, 0,                 1.5,  1.0,        2.5,        1.0 );
  TEST_FP_OP3_H( 9,  fmsub.h, 1,                  11, -1.0,      -12.1,        1.1 );
  TEST_FP_OP3_H(10,  fmsub.h, 0,                -8.0,  2.0,       -5.0,       -2.0 );

  TEST_FP_OP3_H(11, fnmsub.h, 0,                -1.5,  1.0,        2.5,        1.0 );
  TEST_FP_OP3_H(12, fnmsub.h, 1,                 -11, -1.0,      -12.1,        1.1 );
  TEST_FP_OP3_H(13, fnmsub.h, 0,                 8.0,  2.0,       -5.0,       -2.0 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
