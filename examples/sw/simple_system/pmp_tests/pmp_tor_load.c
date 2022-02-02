// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "pmp.h"
#include "simple_system_common.h"

/**
 * PMP regions that are used for load/store and execution permission violation
 * tests.
 *
 * "Volume II: RISC-V Privileged Architectures V20190608-Priv-MSU-Ratified",
 * "3.6 Physical Memory Protection", "Address Matching":
 *
 * "If PMP entry i’s A field is set to TOR, the entry matches any address y
 * such that pmpaddri−1 <= y < pmpaddri. If PMP entry 0’s A field is set to TOR,
 * zero is used for the lower bound, and so it matches any address
 * y < pmpaddr0."
 *
 * To protect an address range that starts above 0 address, the first region
 * we can use is 1.
 */
#define PMP_LOAD_REGION_ID 2

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
static volatile char pmp_load_test_data[PMP_LOAD_RANGE_BUFFER_SIZE];

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

static void pmp_configure_load_tor(void) {
  uintptr_t load_range_start =
      (uintptr_t)&pmp_load_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];

  // Non-inclusive
  uintptr_t load_range_end =
      (uintptr_t)&pmp_load_test_data[PMP_LOAD_RANGE_SIZE];

  pmp_region_config_t config = {
      .lock = kPmpRegionLockLocked,
      .permissions = kPmpRegionPermissionsNone,
  };

  pmp_result_t result = pmp_region_configure_tor(
      PMP_LOAD_REGION_ID, config, load_range_start, load_range_end);
  if (result != kPmpOk) {
    puthex(result);
    puts(" <- error code (Configuration failed)\n");
    sim_halt();
  }
}

int main(void) {
  pmp_load_exception = false;
  char load = pmp_load_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  (void)load;
  if (pmp_load_exception) {
    puts("Not expected load access violation before PMP configuration");
    sim_halt();
  }

  pmp_configure_load_tor();

  pmp_load_exception = false;
  load = pmp_load_test_data[PMP_LOAD_RANGE_BOTTOM_OFFSET];
  if (!pmp_load_exception) {
    puts("Expected load access violation on the bottom of the range load");
    sim_halt();
  }

  pmp_load_exception = false;
  load = pmp_load_test_data[PMP_LOAD_RANGE_TOP_OFFSET];
  if (!pmp_load_exception) {
    puts("Expected load access violation on the top of the range load");
    sim_halt();
  }

  pmp_load_exception = false;
  load = pmp_load_test_data[PMP_LOAD_RANGE_TOP_OFFSET + 1];
  if (pmp_load_exception) {
    puts("Not expected load access violation on top of the range + 1");
    sim_halt();
  }

  puts("SUCCESS!");

  return true;
}
