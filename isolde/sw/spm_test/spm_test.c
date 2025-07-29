/*
 *
 * Copyleft 2025 ISOLDE
 *
 */

// #include <stdio.h>

#include <bsp/simple_system_common.h>
#include <bsp/simple_system_regs.h>
#include <bsp/tinyprintf.h>
#include <bsp/spm.h>

#include <stdlib.h>

#include "cmp_utils.h"
#include "golden.h"



uint32_t read_data[sizeof(golden) / sizeof(golden[0])];
static const int y_flat_size=sizeof(golden) / sizeof(golden[0]) +1 ;
uint32_t y_flat[y_flat_size];

int main(int argc, char *argv[]) {
  int testOK = 1;
  printf("***  \n");
  printf("***  BANK_DATA_WIDTH=0x%08x\n", BANK_DATA_WIDTH);
  printf("***  NUM_BANKS=0x%08x\n", NUM_BANKS);
  printf("***  WIDE_ADDR_ALIGNMENT=0x%08x\n", WIDE_ADDR_ALIGNMENT);
  printf("***  \n");
  uint32_t wide_data_row =
      2;  // just a test position
  uint32_t spm_addr = get_addr_start(wide_data_row);
  uint32_t *src = (uint32_t *)golden;
  uint32_t elems = sizeof(golden) / sizeof(golden[0]);

  uint32_t *dst = read_data;
  // Copy the golden data to SPM
  to_spm(spm_addr, src, elems);
  printf("Copied to SPM at address 0x%08x, %d elements\n", spm_addr, elems);

  // Read back the data from SPM to verify
  from_spm(spm_addr, read_data, elems);
  printf("Copied from SPM  address 0x%08x, %d elements\n", spm_addr, elems);

  // check if the data matches the golden data
  for (uint32_t i = 0; i < elems; ++i) {
    if (src[i] != dst[i]) {
      printf("Error at index %d, expected:0x%08x,got: 0x%08x\n", i, src[i],
             dst[i]);
      testOK = 0;
      break;
    }
  }

  //
  wide_data_row =
      0;  // just a test position, aligned with WIDE_ADDR_ALIGNMENT
  spm_addr = get_addr_start(wide_data_row);

  // golden
  uint32_t golden_spm_addr = spm_addr;
  src = (uint32_t *)golden;
  elems = sizeof(golden) / sizeof(golden[0]);
  uint32_t spm_next_addr = spm_write(spm_addr, src, elems);
  spm_read(y_flat, golden_spm_addr, elems);
  testOK = testOK ? cmp_arrays(golden,y_flat,elems) : testOK;
#ifdef RV_DM_TEST
  while (1) {
    asm volatile("wfi");
  }
#else
  return testOK ? 0x0 : 0xBADC0FFE;
#endif
}