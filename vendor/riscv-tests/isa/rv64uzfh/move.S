# See LICENSE for license details.

#*****************************************************************************
# move.S
#-----------------------------------------------------------------------------
#
# This test verifies that the fmv.h.x, fmv.x.h, and fsgnj[x|n].d instructions
# and the fcsr work properly.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64UF
RVTEST_CODE_BEGIN

  TEST_CASE(2, a1, 1, csrwi fcsr, 1; li a0, 0x1234; fssr a1, a0)
  TEST_CASE(3, a0, 0x34, frsr a0)
  TEST_CASE(4, a0, 0x14, frflags a0)
  TEST_CASE(5, a0, 0x01, csrrwi a0, frm, 2)
  TEST_CASE(6, a0, 0x54, frsr a0)
  TEST_CASE(7, a0, 0x14, csrrci a0, fflags, 4)
  TEST_CASE(8, a0, 0x50, frsr a0)

#define TEST_FSGNJS(n, insn, new_sign, rs1_sign, rs2_sign) \
  TEST_CASE(n, a0, 0x1234 | (-(new_sign) << 15), \
    li a1, ((rs1_sign) << 15) | 0x1234; \
    li a2, -(rs2_sign); \
    fmv.h.x f1, a1; \
    fmv.h.x f2, a2; \
    insn f0, f1, f2; \
    fmv.x.h a0, f0)

  TEST_FSGNJS(10, fsgnj.h, 0, 0, 0)
  TEST_FSGNJS(11, fsgnj.h, 1, 0, 1)
  TEST_FSGNJS(12, fsgnj.h, 0, 1, 0)
  TEST_FSGNJS(13, fsgnj.h, 1, 1, 1)

  TEST_FSGNJS(20, fsgnjn.h, 1, 0, 0)
  TEST_FSGNJS(21, fsgnjn.h, 0, 0, 1)
  TEST_FSGNJS(22, fsgnjn.h, 1, 1, 0)
  TEST_FSGNJS(23, fsgnjn.h, 0, 1, 1)

  TEST_FSGNJS(30, fsgnjx.h, 0, 0, 0)
  TEST_FSGNJS(31, fsgnjx.h, 1, 0, 1)
  TEST_FSGNJS(32, fsgnjx.h, 1, 1, 0)
  TEST_FSGNJS(33, fsgnjx.h, 0, 1, 1)

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
