#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64M
RVTEST_CODE_BEGIN

  # setting the PMP region
  la   t0, pmp_region_start
  srli t1, t0, PMP_SHIFT
  csrw pmpaddr0, t1
  la   t1, pmp_region_end
  srli t1, t1, PMP_SHIFT
  csrw pmpaddr1, t1
  li   t1, (PMP_L | PMP_TOR | PMP_R | PMP_W | PMP_X) << 8
  csrw pmpcfg0, t1

  # access across the boundary between PMP and non-PMP
  lw   t1, -2(t0)

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

.balign 0x1000
pmp_region_start: .zero 0x1000
pmp_region_end:
  TEST_DATA

RVTEST_DATA_END
