// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "pmp.h"
#include "simple_system_common.h"

#define PMP_LOAD_REGION_ID 0

#define PMP_LOAD_RANGE_BUFFER_SIZE 1024
#define PMP_LOAD_RANGE_SIZE 512
#define PMP_LOAD_RANGE_BOTTOM_OFFSET 0
#define PMP_LOAD_RANGE_TOP_OFFSET \
  (PMP_LOAD_RANGE_BOTTOM_OFFSET + PMP_LOAD_RANGE_SIZE - 1)

// These flags are used in the test routine to verify that a corresponding
// interrupt has elapsed, and has been serviced. These are declared as volatile
// since they are referenced in the ISR routine as well as in the main program
// flow.
static volatile bool pmp_load_exception;

/**
 * The buffer that is used for load/store access violation test.
 */
__attribute__((aligned(PMP_LOAD_RANGE_SIZE)))  //
static volatile char pmp_load_store_test_data[PMP_LOAD_RANGE_BUFFER_SIZE];

/**
 * Handles the Load/Store exceptions.
 *
 * Override of the default exception handler.
 */
void simple_exc_handler(void) {
  exception_id_t exception_id = (exception_id_t)get_mcause();
  switch (exception_id) {
    case kLoadAccessFault:
    case kStoreAccessFault:
      set_load_store_exception_retaddr();
      pmp_load_exception = true;
      break;
    default:
      puthex(exception_id);
      puts(" <- exception id (unexpected exception)\n");
      sim_halt();
  }
}

static void pmp_configure_load_napot(void) {
  uintptr_t load_range_start =
      (uintptr_t)&pmp_load_store_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];

  pmp_region_config_t config = {
      .lock = kPmpRegionLockLocked,
      .permissions = kPmpRegionPermissionsNone,
  };

  pmp_result_t result = pmp_region_configure_napot(
      PMP_LOAD_REGION_ID, config, load_range_start, PMP_LOAD_RANGE_SIZE);
  if (result != kPmpOk) {
    puthex(result);
    puts(" <- error code (Configuration failed)\n");
    sim_halt();
  }
}

int main(void) {
  pmp_load_exception = false;
  char load = pmp_load_store_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  (void)load;
  if (pmp_load_exception) {
    puts("Not expected load access violation before PMP configuration");
    sim_halt();
  }

  pmp_configure_load_napot();

  pmp_load_exception = false;
  load = pmp_load_store_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  if (!pmp_load_exception) {
    puts("Expected load access violation on the bottom of the range load");
    sim_halt();
  }

  pmp_load_exception = false;
  load = pmp_load_store_test_data[PMP_LOAD_RANGE_TOP_OFFSET];
  if (!pmp_load_exception) {
    puts("Expected load access violation on the top of the range load");
    sim_halt();
  }

  pmp_load_exception = false;
  load = pmp_load_store_test_data[PMP_LOAD_RANGE_TOP_OFFSET + 1];
  if (pmp_load_exception) {
    puts("Not expected load access violation on top of the range + 1");
    sim_halt();
  }

  puts("SUCCESS!");

  return 0;
}
