// Copyleft 2024 ISOLDE
// https://onnx.ai/onnx/operators/onnx__Conv.html#conv
//
/**
cd $ROOT_DIR/isolde/tca_system
make  PE=onnx TEST=conv2d_test_lca test-clean test-build veri-run
 */

#include <stdint.h>
#ifdef USE_BSP
#include <bsp/tinyprintf.h>
#include <bsp/simple_system_common.h>
#else
#include "tinyprintf.h"
#endif



#define HW_WRITE(value,base,offset) \
    (*(volatile uint32_t *) (base+offset)) =(int) value;
    
#define ONXX_BASE MMADDR_PERF_TTY
#define CMD    0x0
#define  REG_X_PTR 0x0
#define  REG_W_PTR 0x0
#define  REG_Y_PTR 0x0
#define  REG_B_PTR 0x0
#define  REG_X_SHAPE 0x0
#define  REG_W_SHAPE 0x0
#define  REG_PADS 0x0
#define  REG_STRIDES 0x0


float x[2];
float w[2];
float y[2];
float b[2];
int main() {

  volatile int errors = -1;



  uint32_t x_addr = (uint32_t )x;
  uint32_t w_addr = (uint32_t )w;
  uint32_t y_addr = (uint32_t )y;
  uint32_t b_addr = (uint32_t )b;



  tfp_printf("[APP LCA onnx_conv2d] Starting test. Godspeed!\n");
  
  START_PERFCNT(0x1);

  HW_WRITE(x_addr, ONXX_BASE , REG_X_PTR);
  HW_WRITE(w_addr, ONXX_BASE , REG_W_PTR);
  HW_WRITE(y_addr, ONXX_BASE , REG_Y_PTR);
  HW_WRITE(b_addr, ONXX_BASE , REG_B_PTR);
  //
  HW_WRITE(1, ONXX_BASE , REG_X_SHAPE);
  HW_WRITE(2, ONXX_BASE , REG_X_SHAPE);
  HW_WRITE(28, ONXX_BASE , REG_X_SHAPE);
  HW_WRITE(29, ONXX_BASE , REG_X_SHAPE);
//
  HW_WRITE(3, ONXX_BASE , REG_W_SHAPE);
  HW_WRITE(31, ONXX_BASE , REG_W_SHAPE);
  HW_WRITE(32, ONXX_BASE , REG_W_SHAPE);
//  strides
HW_WRITE(11, ONXX_BASE , REG_STRIDES);
HW_WRITE(12, ONXX_BASE , REG_STRIDES);
HW_WRITE(13, ONXX_BASE , REG_STRIDES);
HW_WRITE(14, ONXX_BASE , REG_STRIDES);
// pads
HW_WRITE(10, ONXX_BASE , REG_PADS);
HW_WRITE(101, ONXX_BASE , REG_PADS);
HW_WRITE(102, ONXX_BASE , REG_PADS);
HW_WRITE(103, ONXX_BASE , REG_PADS);
//trigger computation
HW_WRITE(0, ONXX_BASE , CMD);

  STOP_PERFCNT(0x1)
  // Wait for end of computation
  //asm volatile("wfi" ::: "memory");
  printPerfCnt();

  errors = 0;

  tfp_printf("[APP TCA custom-128b] Terminated test with %d errors. See you!\n", errors); 



#ifndef USE_BSP
  *(int *)MMADDR_EXIT = errors;
#endif

  return errors;
}
