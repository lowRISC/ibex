// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*******************************************************************************
 * Directed test to check data independent timing feature
 *
 * This test uses a couple of functions, `count_ones_zeros` and `div_ones_zero`
 * that exhibit data dependent timing. This is via branch instructions in
 * `count_one_zeros` and via divide instructions in `div_ones_zeros`, which are
 * the only two types of instruction with data dependent timing in Ibex.
 *
 * The rest runs multiple iterations of each function providing input from an
 * LFSR, timing each iteration. The test passes where at least 25% of run times
 * differ for each function when data independent timing is disabled and where
 * all run times are identical for each function when data independent timing is
 * enabled.
 *
 * It does a second run with data independent timing enabled and the ICache
 * enabled. This time the functions must be called once with their timing result
 * discarded to warm up the ICache. With that done the function iterations must
 * exhibit identical timing as before for the test to pass.
 * ****************************************************************************/

#include "simple_system_common.h"

extern uint32_t count_ones_zeros(uint32_t n);
extern uint32_t div_ones_zeros(uint32_t n);

#define LFSR_POLY 0x80000057
#define NUM_ITERATIONS 100
#define INITIAL_VAL 0xDEADBEEF

// Simple LFSR step function
uint32_t next_val(uint32_t cur_val) {
  uint32_t bottom_bit = cur_val & 0x1;
  cur_val >>= 1;

  if (bottom_bit) {
    cur_val ^= LFSR_POLY;
  }

  return cur_val;
}

// Enable/disable data independent timing
void set_dit(uint32_t on) {
  if (on) {
    __asm__ volatile("csrsi 0x7c0, 0x2");
  } else {
    __asm__ volatile("csrci 0x7c0, 0x2");
  }
}

// Enable/disable ICache
void set_icache(uint32_t on) {
  if (on) {
    __asm__ volatile("csrsi 0x7c0, 0x1");
  } else {
    __asm__ volatile("csrci 0x7c0, 0x1");
  }
}

// Run NUM_ITERATIONS of count_ones_zeros noting the cycle time from each.
// Return how many times one iteration differed in cycle time from the next.
uint32_t test_b_run_time() {
  uint32_t val = INITIAL_VAL;
  uint32_t mismatches = 0;
  uint32_t last_cycles = count_ones_zeros(val);

  for (int i = 0; i < NUM_ITERATIONS; ++i) {
    val = next_val(val);

    uint32_t cycles = count_ones_zeros(val);
    if (cycles != last_cycles) {
      ++mismatches;
    }

    last_cycles = cycles;
  }

  return mismatches;
}

// Run NUM_ITERATIONS of div_ones_zeros noting the cycle time from each.
// Return how many times one iteration differed in cycle time from the next.
uint32_t test_div_run_time() {
  uint32_t val = INITIAL_VAL;
  uint32_t mismatches = 0;
  uint32_t last_cycles = div_ones_zeros(val);

  for (int i = 0; i < NUM_ITERATIONS; ++i) {
    val = next_val(val);

    uint32_t cycles = div_ones_zeros(val);
    if (cycles != last_cycles) {
      ++mismatches;
    }

    last_cycles = cycles;
  }

  return mismatches;
}

int main(void) {
  uint32_t mismatches;
  pcount_enable(1);

  set_dit(0);
  mismatches = test_b_run_time();
  if (mismatches < (NUM_ITERATIONS / 4)) {
    puts(
        "FAILURE: Too few cycle mismatches seen for branch test when DIT "
        "disabled: 0x");
    puthex(mismatches);
    return 1;
  }

  set_dit(1);
  mismatches = test_b_run_time();
  if (mismatches != 0) {
    puts("FAILURE: Cycle mismatches seen for branch test when DIT enabled: 0x");
    puthex(mismatches);
    return 1;
  }

  set_icache(1);
  // Warm up ICache
  test_b_run_time();

  // Run test with ICache enabled
  mismatches = test_b_run_time();
  if (mismatches != 0) {
    puts(
        "FAILURE: Cycle mismatches seen for branch test when DIT and ICache "
        "enabled: 0x");
    puthex(mismatches);
    return 1;
  }

  set_icache(0);

  set_dit(0);
  mismatches = test_div_run_time();
  if (mismatches < (NUM_ITERATIONS / 4)) {
    puts(
        "FAILURE: Too few cycle mismatches seen for divide test when DIT "
        "disabled: 0x");
    puthex(mismatches);
    return 1;
  }

  set_dit(1);
  mismatches = test_div_run_time();
  if (mismatches != 0) {
    puts("FAILURE: Cycle mismatches seen for divide test when DIT enabled: 0x");
    puthex(mismatches);
    return 1;
  }

  set_icache(1);
  // Warm up ICache
  test_div_run_time();

  // Run test with ICache enabled
  mismatches = test_div_run_time();
  if (mismatches != 0) {
    puts(
        "FAILURE: Cycle mismatches seen for divide test when DIT and ICache "
        "enabled: 0x");
    puthex(mismatches);
    return 1;
  }

  puts("PASS: All test sequences behaved as expected");
  return 0;
}
