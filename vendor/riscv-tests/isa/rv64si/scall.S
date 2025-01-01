# See LICENSE for license details.

#*****************************************************************************
# scall.S
#-----------------------------------------------------------------------------
#
# Test syscall trap.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64S
RVTEST_CODE_BEGIN

#ifdef __MACHINE_MODE
  #define sscratch mscratch
  #define sstatus mstatus
  #define scause mcause
  #define stvec mtvec
  #define sepc mepc
  #define sret mret
  #define stvec_handler mtvec_handler
  #undef SSTATUS_SPP
  #define SSTATUS_SPP MSTATUS_MPP
#endif

  li TESTNUM, 2

  # This is the expected trap code.
  li t1, CAUSE_USER_ECALL

#ifdef __MACHINE_MODE
  # If running in M mode, use mstatus.MPP to check existence of U mode.
  # Otherwise, if in S mode, then U mode must exist and we don't need to check.
  li t0, MSTATUS_MPP
  csrc mstatus, t0
  csrr t2, mstatus
  and t0, t0, t2
  beqz t0, 1f

  # If U mode doesn't exist, mcause should indicate ECALL from M mode.
  li t1, CAUSE_MACHINE_ECALL
#endif

1:
  li t0, SSTATUS_SPP
  csrc sstatus, t0
  la t0, 1f
  csrw sepc, t0
  sret
1:

  li TESTNUM, 1
do_scall:
  scall
  j fail

  TEST_PASSFAIL

# Depending on the test environment, the M-mode version of this test might
# not actually invoke the following handler.  Instead, the usual ECALL
# handler in the test environment might detect the CAUSE_USER_ECALL or
# CAUSE_MACHINE_ECALL exception and mark the test as having passed.
# Either way, we'll get the coverage we desire: such a handler must check
# both mcause and TESTNUM, just like the following handler.
  .align 2
  .global stvec_handler
stvec_handler:
  csrr t0, scause
  # Check if CLIC mode
  csrr t2, stvec
  andi t2, t2, 2
  # Skip masking if non-CLIC mode
  beqz t2, skip_mask 
  andi t0, t0, 255
skip_mask:
  bne t0, t1, fail
  la t2, do_scall
  csrr t0, sepc
  bne t0, t2, fail
  j pass

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
