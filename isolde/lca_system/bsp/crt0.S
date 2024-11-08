# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0



.section .text

default_exc_handler:
  jal x0, simple_exc_handler

#timer_handler:
#  jal x0, simple_exc_handler

reset_handler:
  /* set all registers to zero */
  mv  x1, x0
  mv  x2, x1
  mv  x3, x1
  mv  x4, x1
  mv  x5, x1
  mv  x6, x1
  mv  x7, x1
  mv  x8, x1
  mv  x9, x1
  mv x10, x1
  mv x11, x1
  mv x12, x1
  mv x13, x1
  mv x14, x1
  mv x15, x1
  mv x16, x1
  mv x17, x1
  mv x18, x1
  mv x19, x1
  mv x20, x1
  mv x21, x1
  mv x22, x1
  mv x23, x1
  mv x24, x1
  mv x25, x1
  mv x26, x1
  mv x27, x1
  mv x28, x1
  mv x29, x1
  mv x30, x1
  mv x31, x1

  .global _start
_start:
 
  # Enabling interrupts globally.  mstatus.MIE
  li      t0, 0x8
  csrrs   zero, mstatus, t0
  # Enabling  SW interrupt (mie[3]) , see https://ibex-core.readthedocs.io/en/latest/03_reference/cs_registers.html#machine-interrupt-enable-register-mie
  li      t0, 0x8
  csrrs   zero, mie, t0


  /* Stack initialization */
  la   x2, _stack_start
  andi sp, x2, ~0x7      //aligning the stack pointer (sp) to an 8-byte boundary 

  /* clear BSS */
  la x26, _bss_start
  la x27, _bss_end

  bge x26, x27, zero_loop_end

zero_loop:
  sw x0, 0(x26)
  addi x26, x26, 4
  ble x26, x27, zero_loop
zero_loop_end:


main_entry:
  /* jump to startup program entry  */
  addi a0, x0, 0
  addi a1, x0, 0
  jal x1, startup
  /* If execution ends up here just put the core to sleep */
sleep_loop:
  wfi
  j sleep_loop

/* =================================================== [ exceptions ] === */
/* This section has to be down here, since we have to disable rvc for it  */

  .section .vectors, "ax"
  .option norvc;

  // All unimplemented interrupts/exceptions go to the default_exc_handler.
  .org 0x00
  .rept 31
  jal x0, default_exc_handler
  .endr

  // reset vector
  .org 0x80
  jal x0, reset_handler
