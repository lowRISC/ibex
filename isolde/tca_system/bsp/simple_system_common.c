// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "simple_system_common.h"
#include "tinyprintf.h"



// see tb/core/mm_ram.sv
void _Exit(int exit_code){

DEV_WRITE(MMADDR_EXIT, (uint32_t)exit_code); 
 while (1) {
        asm volatile ("wfi");
    }
}

 void _putcf (void *, char c) {
  DEV_WRITE(MMADDR_PRINT, (uint32_t)c); 
}


int putchar(char c){
  _putcf (0,  c);
  return 1;
}
void puthex(uint32_t h) {
  int cur_digit;
  // Iterate through h taking top 4 bits each time and outputting ASCII of hex
  // digit for those 4 bits
  for (int i = 0; i < 8; i++) {
    cur_digit = h >> 28;

    if (cur_digit < 10)
      putchar('0' + cur_digit);
    else
      putchar('A' - 10 + cur_digit);

    h <<= 4;
  }
}


void sim_halt() { DEV_WRITE(MMADDR_EXIT, 1); }

void pcount_reset() {
  asm volatile(
      "csrw minstret,       x0\n"
      "csrw mcycle,         x0\n"
      "csrw mhpmcounter3,   x0\n"
      "csrw mhpmcounter4,   x0\n"
      "csrw mhpmcounter5,   x0\n"
      "csrw mhpmcounter6,   x0\n"
      "csrw mhpmcounter7,   x0\n"
      "csrw mhpmcounter8,   x0\n"
      "csrw mhpmcounter9,   x0\n"
      "csrw mhpmcounter10,  x0\n"
      "csrw mhpmcounter11,  x0\n"
      "csrw mhpmcounter12,  x0\n"
      "csrw mhpmcounter13,  x0\n"
      "csrw mhpmcounter14,  x0\n"
      "csrw mhpmcounter15,  x0\n"
      "csrw mhpmcounter16,  x0\n"
      "csrw mhpmcounter17,  x0\n"
      "csrw mhpmcounter18,  x0\n"
      "csrw mhpmcounter19,  x0\n"
      "csrw mhpmcounter20,  x0\n"
      "csrw mhpmcounter21,  x0\n"
      "csrw mhpmcounter22,  x0\n"
      "csrw mhpmcounter23,  x0\n"
      "csrw mhpmcounter24,  x0\n"
      "csrw mhpmcounter25,  x0\n"
      "csrw mhpmcounter26,  x0\n"
      "csrw mhpmcounter27,  x0\n"
      "csrw mhpmcounter28,  x0\n"
      "csrw mhpmcounter29,  x0\n"
      "csrw mhpmcounter30,  x0\n"
      "csrw mhpmcounter31,  x0\n"
      "csrw minstreth,      x0\n"
      "csrw mcycleh,        x0\n"
      "csrw mhpmcounter3h,  x0\n"
      "csrw mhpmcounter4h,  x0\n"
      "csrw mhpmcounter5h,  x0\n"
      "csrw mhpmcounter6h,  x0\n"
      "csrw mhpmcounter7h,  x0\n"
      "csrw mhpmcounter8h,  x0\n"
      "csrw mhpmcounter9h,  x0\n"
      "csrw mhpmcounter10h, x0\n"
      "csrw mhpmcounter11h, x0\n"
      "csrw mhpmcounter12h, x0\n"
      "csrw mhpmcounter13h, x0\n"
      "csrw mhpmcounter14h, x0\n"
      "csrw mhpmcounter15h, x0\n"
      "csrw mhpmcounter16h, x0\n"
      "csrw mhpmcounter17h, x0\n"
      "csrw mhpmcounter18h, x0\n"
      "csrw mhpmcounter19h, x0\n"
      "csrw mhpmcounter20h, x0\n"
      "csrw mhpmcounter21h, x0\n"
      "csrw mhpmcounter22h, x0\n"
      "csrw mhpmcounter23h, x0\n"
      "csrw mhpmcounter24h, x0\n"
      "csrw mhpmcounter25h, x0\n"
      "csrw mhpmcounter26h, x0\n"
      "csrw mhpmcounter27h, x0\n"
      "csrw mhpmcounter28h, x0\n"
      "csrw mhpmcounter29h, x0\n"
      "csrw mhpmcounter30h, x0\n"
      "csrw mhpmcounter31h, x0\n");
}

unsigned int get_mepc() {
  uint32_t result;
  __asm__ volatile("csrr %0, mepc;" : "=r"(result));
  return result;
}

unsigned int get_mcause() {
  uint32_t result;
  __asm__ volatile("csrr %0, mcause;" : "=r"(result));
  return result;
}

unsigned int get_mtval() {
  uint32_t result;
  __asm__ volatile("csrr %0, mtval;" : "=r"(result));
  return result;
}

void simple_exc_handler(void) {
  #if 0
    volatile register int a7 asm("a7");
  
  // Check if A7 equals 93
  //https://jborza.com/post/2021-05-11-riscv-linux-syscalls/
  if (a7 == 93) {
#else
  int result;
  asm volatile ("mv %0, a7" : "=r"(result));
  // Check if A7 equals 93
  //https://jborza.com/post/2021-05-11-riscv-linux-syscalls/
  if (result == 93) {
#endif  
    printf("exit()\n");
    printf("======\n");
  }else{
    printf("EXCEPTION!!!\n");
    printf("============\n");
    printf("MEPC:   0x");
    puthex(get_mepc());
    printf("\nMCAUSE: 0x");
    puthex(get_mcause());
    printf("\nMTVAL:  0x");
    puthex(get_mtval());
    putchar('\n');
  }
  sim_halt();

  while(1);
}


void printPerfCnt(){
   int perfcnt_id =  *(volatile int *) MMADDR_PERF_COUNTERS;
   int perfcnt_cycles =  *(volatile int *) (MMADDR_PERF_COUNTERS+4);
   printf("Terminated test  %d in %d cycles\n",perfcnt_id,perfcnt_cycles);
   //
   int perfcnt_imem_wr =  *(volatile int *) (MMADDR_PERF_COUNTERS+0x8);
   int perfcnt_imem_rd =  *(volatile int *) (MMADDR_PERF_COUNTERS+0xC);
   int perfcnt_dmem_wr =  *(volatile int *) (MMADDR_PERF_COUNTERS+0x10);
   int perfcnt_dmem_rd =  *(volatile int *) (MMADDR_PERF_COUNTERS+0x14);
   int perfcnt_stack_mem_wr =  *(volatile int *) (MMADDR_PERF_COUNTERS+0x18);
   int perfcnt_stack_mem_rd =  *(volatile int *) (MMADDR_PERF_COUNTERS+0x1C);
   printf("  \
    reads  [imemory] = %d \n  \
    writes [dmemory] = %d \n  \
    reads  [dmemory] = %d \n  \
    writes [stack] = %d \n  \
    reads  [stack] = %d \n\n  \
    ", perfcnt_imem_rd, perfcnt_dmem_wr,perfcnt_dmem_rd,perfcnt_stack_mem_wr, perfcnt_stack_mem_rd);
}