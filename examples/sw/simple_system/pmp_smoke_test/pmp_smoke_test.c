// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Basic smoke test for PMP. The test sets up a read-only PMP region then tries
// to write to it. It is intended for use with an external checking method (such
// as the Ibex co-simulation system) and does not report pass or fail.

volatile unsigned int test_int = 10;

// Locked read only for lowest region, NA4 matching
#define TEST_PMPCFG0 0x91

int main(int argc, char **argv) {
  unsigned int pmpaddr0 = ((unsigned int)&test_int) >> 2;

  __asm__ volatile(
      "csrw pmpaddr0, %1\n"
      "csrw pmpcfg0, %0\n"
      :
      : "r"(TEST_PMPCFG0), "r"(pmpaddr0));

  test_int = 12;

  return 0;
}
