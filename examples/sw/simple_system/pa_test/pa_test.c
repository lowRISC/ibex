// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "simple_system_common.h"

#define PMP_NAPOT 0x18
#define PMP_R     0x01
#define PMP_W     0x02
#define PMP_X     0x04

#define MSTATUS_MPP_M (3 << 11)
#define MSTATUS_MPP_U (0 << 11)


typedef struct  {
  uintptr_t pointer0;
  uintptr_t pointer1;
} auth_ptr_t;


void setup_pakey() {
  // Set the key for PA in CSR
  uint32_t key = 0xdeadbeef;
  asm volatile ("csrw 0x7c2, %[key];"
                "csrw 0x7c3, %[key];"
                "csrw 0x7c4, %[key];"
                "csrw 0x7c5, %[key];"
                : : [key] "r" (key) :);
}

void setup_pmp() {
  // 0x00000000 ~ 0x0FFFFFFF is accessible
  uint32_t base_addr  = 0x0;
  uint32_t size       = 1 << 30;
  uint32_t napot_size = (size / 2) - 1;
  uint32_t pmpaddr = (base_addr + napot_size) >> 2;
  uint32_t pmpcfg = PMP_NAPOT | PMP_R | PMP_W | PMP_X;
  asm volatile ("csrw pmpaddr0, %0;"
                "csrw pmpcfg0, %1;"
                : : "r" (pmpaddr), "r" (pmpcfg) :);
}


auth_ptr_t pac(auth_ptr_t ptr, uint32_t context) {
  asm volatile (".insn r 0x0b, 0, 0, %[pointer1], %[pointer0], %[context];"
                : [pointer0] "+r"  (ptr.pointer0), [pointer1] "=r" (ptr.pointer1)
                : [context] "r" (context)
  );
  return ptr;
}

auth_ptr_t aut(auth_ptr_t ptr, uint32_t context) {
  asm volatile (".insn r4 0x0b, 1, 0, %[pointer0], %[pointer0], %[pointer1], %[context];"
                : [pointer0] "+r" (ptr.pointer0)
                : [pointer1] "r" (ptr.pointer1), [context] "r" (context)
  );
  return ptr;
}

void print_auth_ptr(auth_ptr_t ptr) {
  puts("pointer0: ");
  puthex(ptr.pointer0);
  putchar('\n');
  puts("pointer1: ");
  puthex(ptr.pointer1);
  putchar('\n');
}


// Test for pac and aut instruction
void test_pointer_authentication() {
  auth_ptr_t ptr = { .pointer0 = 0x1000, .pointer1 = 0x0 };
  const uint32_t context = 0xffff;

  // Execute PAC instruction
  auth_ptr_t pac_ptr = pac(ptr,     context);
  print_auth_ptr(pac_ptr);

  // Execute AUT instruction
  auth_ptr_t aut_ptr = aut(pac_ptr, context);
  print_auth_ptr(aut_ptr);

  // Check if the pointer authentication scenario is correct
  if (ptr.pointer0 != aut_ptr.pointer0) {
    puts("Error: Pointer Authentication\n");
  }
}

// Test whether pmp error occurs when accessing with unauthenticated pointer
void test_pmp_error() {
  const int data = 'A';
  auth_ptr_t ptr = { .pointer0 = (uintptr_t)&data, .pointer1 = 0x0 };
  const uint32_t context = 0xffff;

  auth_ptr_t pac_ptr = pac(ptr, context);
  // Access data using unauthenticated pointer
  *(int*)pac_ptr.pointer0 = 'B'; // <- Error occurs due to use of unauthenticated pointer
}

void test() {
  test_pointer_authentication();
  test_pmp_error();

  // Stop simulation
  sim_halt();
}


int main(int argc, char **argv) {
  setup_pakey();
  setup_pmp();

  // from M mode to U mode
  uint32_t mstatus;
  asm volatile ("csrr %0, mstatus" : "=r" (mstatus));
  mstatus = (mstatus & ~MSTATUS_MPP_M) | MSTATUS_MPP_U;
  asm volatile ("csrw mstatus, %0;"
                "csrw mepc, %1;"
                "mret;"
                 : : "r" (mstatus), "r" (test));
  return 0;
}
