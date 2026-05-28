# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This test verifies mcounteren CSR functionality by sweeping multiple bit
# patterns to ensure User-mode access to all 64 performance counters is
# correctly gated. It confirms that allowed registers read successfully,
# while disabled registers securely trigger illegal instruction exceptions.

#include "custom_macros.h"
#include "riscv_test.h"
#include "test_macros.h"

# Register Allocation:
# s1: Expected instruction execution state(1 = should succeed, 0 = should trap)
# s2: Readback snapshot of valid mcounteren bits
# s3: Subroutine return address backup tracking register(ra)
# s4: Label pointing to the next macro boundary
# s5: Subroutine continuation target pointer used upon full block completion

.macro RUN_CSR_TEST idx, csr_addr
  # Check if this counter is configured to be accessible
  # Get position at which to check mcounteren bit for this counter
  li    t0, \csr_addr
  andi  t0, t0, 0x1F
  # Create mask from position
  li    t1, 1
  sll   t1, t1, t0
  and   t1, s2, t1
  # s1 = 1 if counter is enabled and should succeed cleanly
  snez  s1, t1

  # Set next test label for the handler
  la    s4, next_test_\idx

  # Read counter.This should trap if s1 == 0 and succeed if s1 == 1
  csrr  t0, \csr_addr
  # If the counter was supposed to trap but didn't, fail immediately
  beqz  s1, fail
  # Continue to next test
next_test_\idx:
.endm

.macro RUN_ALL_CSR_TESTS
  # Lower 32 Bits of Performance Counters
  RUN_CSR_TEST  0, 0xC00   # cycle
  RUN_CSR_TEST  1, 0xC01   # time
  RUN_CSR_TEST  2, 0xC02   # instret
  RUN_CSR_TEST  3, 0xC03   # hpmcounter3
  RUN_CSR_TEST  4, 0xC04
  RUN_CSR_TEST  5, 0xC05
  RUN_CSR_TEST  6, 0xC06
  RUN_CSR_TEST  7, 0xC07
  RUN_CSR_TEST  8, 0xC08
  RUN_CSR_TEST  9, 0xC09
  RUN_CSR_TEST 10, 0xC0A
  RUN_CSR_TEST 11, 0xC0B
  RUN_CSR_TEST 12, 0xC0C
  RUN_CSR_TEST 13, 0xC0D
  RUN_CSR_TEST 14, 0xC0E
  RUN_CSR_TEST 15, 0xC0F
  RUN_CSR_TEST 16, 0xC10
  RUN_CSR_TEST 17, 0xC11
  RUN_CSR_TEST 18, 0xC12
  RUN_CSR_TEST 19, 0xC13
  RUN_CSR_TEST 20, 0xC14
  RUN_CSR_TEST 21, 0xC15
  RUN_CSR_TEST 22, 0xC16
  RUN_CSR_TEST 23, 0xC17
  RUN_CSR_TEST 24, 0xC18
  RUN_CSR_TEST 25, 0xC19
  RUN_CSR_TEST 26, 0xC1A
  RUN_CSR_TEST 27, 0xC1B
  RUN_CSR_TEST 28, 0xC1C
  RUN_CSR_TEST 29, 0xC1D
  RUN_CSR_TEST 30, 0xC1E
  RUN_CSR_TEST 31, 0xC1F   # hpmcounter31
  # Upper 32 Bits of Performance Counters
  RUN_CSR_TEST 32, 0xC80   # cycleh
  RUN_CSR_TEST 33, 0xC81   # timeh
  RUN_CSR_TEST 34, 0xC82   # instreth
  RUN_CSR_TEST 35, 0xC83   # hpmcounter3h
  RUN_CSR_TEST 36, 0xC84
  RUN_CSR_TEST 37, 0xC85
  RUN_CSR_TEST 38, 0xC86
  RUN_CSR_TEST 39, 0xC87
  RUN_CSR_TEST 40, 0xC88
  RUN_CSR_TEST 41, 0xC89
  RUN_CSR_TEST 42, 0xC8A
  RUN_CSR_TEST 43, 0xC8B
  RUN_CSR_TEST 44, 0xC8C
  RUN_CSR_TEST 45, 0xC8D
  RUN_CSR_TEST 46, 0xC8E
  RUN_CSR_TEST 47, 0xC8F
  RUN_CSR_TEST 48, 0xC90
  RUN_CSR_TEST 49, 0xC91
  RUN_CSR_TEST 50, 0xC92
  RUN_CSR_TEST 51, 0xC93
  RUN_CSR_TEST 52, 0xC94
  RUN_CSR_TEST 53, 0xC95
  RUN_CSR_TEST 54, 0xC96
  RUN_CSR_TEST 55, 0xC97
  RUN_CSR_TEST 56, 0xC98
  RUN_CSR_TEST 57, 0xC99
  RUN_CSR_TEST 58, 0xC9A
  RUN_CSR_TEST 59, 0xC9B
  RUN_CSR_TEST 60, 0xC9C
  RUN_CSR_TEST 61, 0xC9D
  RUN_CSR_TEST 62, 0xC9E
  RUN_CSR_TEST 63, 0xC9F   # hpmcounter31h
.endm

# -----------------------------------------------------------------------
#  Main Verification Blocks
# -----------------------------------------------------------------------

RVTEST_RV32M
RVTEST_CODE_BEGIN

  la   t0, mtvec_handler
  csrw mtvec, t0

  # Verify default power - on reset state
  csrr  t0, mcounteren
  bnez  t0, fail

  # Verify that we can write to mcounteren and read back the expected value
  li    t0, 0x1
  csrw  mcounteren, t0
  csrr  t1, mcounteren
  bne   t1, t0, fail

  # Verify time enable bit is hardwired to zero while other bits are sticky
  li    t0, 0x7
  csrw  mcounteren, t0
  csrr  t1, mcounteren
  xori  t1, t1, 0x5
  bnez  t1, fail

  # Sweep with all implemented counters enabled
  li    t0, 0xFFFFFFFF
  csrw  mcounteren, t0
  csrr  s2, mcounteren
  jal   ra, run_all_csr_tests

  # Sweep with all counters disabled
  csrwi mcounteren, 0
  csrr  s2, mcounteren
  jal   ra, run_all_csr_tests

  # Sweep using alternating bits
  li    t0, 0x55555555
  csrw  mcounteren, t0
  csrr  s2, mcounteren
  jal   ra, run_all_csr_tests

  # Sweep using arbitrary custom mask
  li    t0, 0xCD609E2D
  csrw  mcounteren, t0
  csrr  s2, mcounteren
  jal   ra, run_all_csr_tests

  # If execution hits this line, all pattern sweeps successfully completed
  csrwi mcounteren, 0
  j     pass

  TEST_PASSFAIL

# -----------------------------------------------------------------------
#  Evaluation Subroutine
# -----------------------------------------------------------------------
run_all_csr_tests:
  mv    s3, ra
  la    s5, post_all_tests
  # Drop to U-mode once per pattern to execute the continuous instruction stream
  SWITCH_TO_U_MODE_LABEL(u_mode_sweep_entry)

.balign 4
u_mode_sweep_entry:
  RUN_ALL_CSR_TESTS

  # Reaching this line implies all 32 checks passed cleanly
  ecall

post_all_tests:
  mv    ra, s3
  ret

# -----------------------------------------------------------------------
#  Exception Trap Handler
# -----------------------------------------------------------------------
.balign 256
mtvec_handler:
  csrr  t0, mcause

  # mcause 8 = Environment Call from U-mode (stream finished successfully)
  li    t1, 8
  beq   t0, t1, handle_ecall

  # mcause 2 = Illegal Instruction
  li    t1, 2
  # Drop out to failure trap on all unexpected exceptions
  bne   t0, t1, fail

  # If the register was supposed to be accessible (s1 == 1) but faulted, fail
  bnez  s1, fail

  # Valid hardware restriction exception. Safely continue to next macro block
  csrw  mepc, s4
  mret

handle_ecall:
  # All unrolled checks passed. Safely return back to M-mode context runner
  csrw  mepc, s5
  li    t0, 0x1800
  csrs  mstatus, t0
  mret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA
RVTEST_DATA_END
