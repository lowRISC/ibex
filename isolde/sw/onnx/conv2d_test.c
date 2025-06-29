// Copyleft 2024 ISOLDE
// https://onnx.ai/onnx/operators/onnx__Conv.html#conv
//
/**
cd $ROOT_DIR/isolde/tca_system
make  PE=onnx TEST=conv2d_test test-clean test-build veri-run
 */

#include <stdint.h>
#ifdef USE_BSP
#include <bsp/tinyprintf.h>
#include <bsp/simple_system_common.h>
#else
#include "tinyprintf.h"
#endif

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


  tfp_printf("[APP TCA onnx_conv2d] Starting test. Godspeed!\n");
  
  START_PERFCNT(0x1)
  asm volatile("addi t2, %0, 0" ::"r"(y_addr));   //x7
  asm volatile("addi t1, %0, 0" ::"r"(x_addr));  //x6 
  asm volatile("addi t0, %0, 0" ::"r"(w_addr));  //x5
  asm volatile("addi t3, %0, 0" ::"r"(b_addr)); //x28

  asm volatile("ld4xi32 Q1, 1, 1, 1, 1");
  asm volatile("ld4xi32 Q2, 1, 0, 1, 0");
  asm volatile("ld3xi32 Q3, 1, 3, 3");
  asm volatile("ld4xi32 Q4, 1, 1, 28, 28");
  asm volatile("onnx.conv2d.f32 t2, Q0, t1, Q4, t0, Q3, t3, Q2, Q1");
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
