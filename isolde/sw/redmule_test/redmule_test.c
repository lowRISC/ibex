/*
 *
 * Copyleft 2025 ISOLDE
 *
 */

// #include <stdio.h>
#include <bsp/simple_system_common.h>
#include <bsp/simple_system_regs.h>
#include <bsp/spm.h>
#include <bsp/tinyprintf.h>

#include "cmp_utils.h"
#include "redmule_utils.h"
#include "archi_redmule.h"
#include "golden.h"
#include "hal_redmule.h"
#include "w_input.h"
#include "x_input.h"
#include "y_input.h"

static const int y_flat_size=sizeof(golden) / sizeof(golden[0]) +1 ;
uint32_t y_flat[y_flat_size];



uint32_t test_hwe(uint32_t x, uint32_t w, uint32_t y) {
  uint32_t errors = 0;

  const uint32_t cfg_reg0 = ((K_SIZE << 16) | (M_SIZE << 0));
  const uint32_t cfg_reg1 = (N_SIZE << 0);
  const uint32_t arith_reg = (GEMM << 10) | (1 << 7);
  // START_TIMING(REDMULE_LCA);

  printf("[SPM LCA ] Starting test. Godspeed!\n");
  START_PERFCNT(0x1)
  HWPE_WRITE((unsigned int)x, REDMULE_REG_OFFS + REDMULE_REG_X_PTR);
  HWPE_WRITE((unsigned int)w, REDMULE_REG_OFFS + REDMULE_REG_W_PTR);
  HWPE_WRITE((unsigned int)y, REDMULE_REG_OFFS + REDMULE_REG_Z_PTR);
  //
  HWPE_WRITE(cfg_reg0, REDMULE_REG_OFFS + REDMULE_MCFG0_PTR);
  HWPE_WRITE(cfg_reg1, REDMULE_REG_OFFS + REDMULE_MCFG1_PTR);
  //
  HWPE_WRITE(arith_reg, REDMULE_REG_OFFS + REDMULE_ARITH_PTR);
  // trigger job();
  HWPE_WRITE(0, REDMULE_TRIGGER);
  STOP_PERFCNT(0x1)
  START_PERFCNT(0x2)
  // Wait for end of computation
  asm volatile("wfi" ::: "memory");
  STOP_PERFCNT(0x2)
  printPerfCnt();

  // errors = redmule16_compare_int(y, golden, M_SIZE * K_SIZE / 2);
  uint32_t elems = sizeof(y_flat) / sizeof(y_flat[0]);
  spm_read(y_flat, y, elems);
  errors = redmule16_compare_int(y_flat, golden, M_SIZE * K_SIZE / 2);

  printf("[SPM LCA] Terminated test with %d errors. See you!\n", errors);
  return errors;
}


uint32_t x_spm_addr, y_spm_addr, w_spm_addr, golden_spm_addr, spm_next_addr;
uint32_t x_size =
    (sizeof(x_inp) / sizeof(x_inp[0])) / 2;  // size in 32 bits elements
uint32_t y_size =
    (sizeof(y_inp) / sizeof(y_inp[0])) / 2;  // size in 32 bits elements
uint32_t w_size =
    (sizeof(w_inp) / sizeof(w_inp[0])) / 2;  // size in 32 bits elements

int main(int argc, char *argv[]) {
  int testOK = 1;
  uint32_t errors;
  printf("***  \n");
  printf("***  BANK_DATA_WIDTH=0x%08x\n", BANK_DATA_WIDTH);
  printf("***  NUM_BANKS=0x%08x\n", NUM_BANKS);
  printf("***  WIDE_ADDR_ALIGNMENT=0x%08x\n", WIDE_ADDR_ALIGNMENT);
  printf("***  \n");
  uint32_t wide_data_row =
      0;  // just a test position, aligned with WIDE_ADDR_ALIGNMENT
  uint32_t spm_addr, spm_next_addr = get_addr_start(wide_data_row);
  uint32_t *src;
  uint32_t elems;
 

  
  // x_inp
  x_spm_addr = spm_next_addr;
  spm_addr = x_spm_addr;
  src = (uint32_t *)x_inp;
  elems = x_size;
  spm_next_addr = spm_write(spm_addr, src, elems);

  // w_input
  w_spm_addr = spm_next_addr;
  spm_addr = w_spm_addr;
  src = (uint32_t *)w_inp;
  elems = w_size;
  spm_next_addr = spm_write(spm_addr, src, elems);

  // y_inp
  y_spm_addr = spm_next_addr;
  spm_addr = y_spm_addr;
  src = (uint32_t *)y_inp;
  elems = y_size;
  spm_next_addr = spm_write(spm_addr, src, elems);



  errors = test_hwe(x_spm_addr, w_spm_addr, y_spm_addr);
  

  return errors ?  0xBADC0FFE :0x0;

}