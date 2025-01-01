// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*******************************************************************************
 * Directed test to check dummy instruction insertion feature
 *
 * This test uses a function `busy_work` which does some computation based on 3
 * input uint32_t arrays writing a result into a uint32_t output array.
 * `busy_work` is run over multiple iterations, timing each. The function does
 * not exhibit data dependent timing behaviour so the test passes when every run
 * takes an identical time with dummy instruction insertion disabled and every
 * run takes a different time with dummy instruction insertion enabled.
 ******************************************************************************/

#include "simple_system_common.h"

extern uint32_t busy_work(uint32_t num_vals, uint32_t *in_1, uint32_t *in_2,
                          uint32_t *in_3, uint32_t *out);

#define LFSR_POLY 0x80000057
#define INITIAL_VAL 0xDEADBEEF

#define NUM_VALUES 100
#define NUM_ITERATIONS 5

uint32_t next_val(uint32_t cur_val) {
  uint32_t bottom_bit = cur_val & 0x1;
  cur_val >>= 1;

  if (bottom_bit) {
    cur_val ^= LFSR_POLY;
  }

  return cur_val;
}

uint32_t lfsr_value = INITIAL_VAL;

void set_dummy_instr(uint32_t on) {
  if (on) {
    __asm__ volatile("csrsi 0x7c0, 0x4");
  } else {
    __asm__ volatile("csrci 0x7c0, 0x4");
  }
}

uint32_t in_1[100];
uint32_t in_2[100];
uint32_t in_3[100];
uint32_t out[100];

void setup_values() {
  for (int i = 0; i < NUM_VALUES; ++i) {
    in_1[i] = lfsr_value;
    lfsr_value = next_val(lfsr_value);
    in_2[i] = lfsr_value;
    lfsr_value = next_val(lfsr_value);
    in_3[i] = lfsr_value;
    lfsr_value = next_val(lfsr_value);
  }
}

uint32_t run_busy_work_test(uint32_t iterations) {
  uint32_t last_cycles;
  uint32_t mismatches = 0;

  setup_values();
  last_cycles = busy_work(NUM_VALUES, in_1, in_2, in_3, out);
  for (int i = 0; i < iterations - 1; ++i) {
    uint32_t cycles = busy_work(NUM_VALUES, in_1, in_2, in_3, out);

    if (cycles != last_cycles) {
      mismatches++;
    }

    last_cycles = cycles;
  }

  return mismatches;
}

int main(void) {
  uint32_t mismatches;
  pcount_enable(1);

  set_dummy_instr(0);
  mismatches = run_busy_work_test(NUM_ITERATIONS);
  if (mismatches != 0) {
    puts("FAILURE: Cycle mismatches seen when dummy instructions disabled: ");
    puthex(mismatches);
    return 1;
  }

  set_dummy_instr(1);
  mismatches = run_busy_work_test(NUM_ITERATIONS);
  if (mismatches != NUM_ITERATIONS - 1) {
    puts(
        "FAILURE: Not enough Cycle mismatches seen when dummy instructions "
        "enabled: ");
    puthex(mismatches);
    return 1;
  }

  puts("PASS: All test sequences behaved as expected");

  return 0;
}
