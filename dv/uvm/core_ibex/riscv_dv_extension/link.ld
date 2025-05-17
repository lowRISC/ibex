/* Copyright lowRISC contributors.
   Licensed under the Apache License, Version 2.0, see LICENSE for details.
   SPDX-License-Identifier: Apache-2.0 */

/*
 * This linker script maps the generated debug test code into a discrete region
 * of the address space, representative of a discrete external debug module.
 * i.e. when +discrete_debug_module=1
 */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

MEMORY
{
  ram  : ORIGIN = 0x80000000, LENGTH = 0x100000
  dm   : ORIGIN = 0x1A110000, LENGTH = 0x1000
}

_dm_scratch_len = 0x100;

/* PHDRS */
/* { */
/*   debug_module PT_LOAD ; */
/* } */

SECTIONS
{
  .text : {
    *(.text)
    . = ALIGN(0x1000);
  } >ram
  .tohost : {
    . = ALIGN(4);
    *(.tohost)
    . = ALIGN(0x1000);
  } >ram
  .page_table : {
    *(.page_table)
  } >ram
  .data : {
    *(.data)
  } >ram
  .user_stack : {
    *(.user_stack)
  } >ram
  .kernel_data : {
    *(.kernel_data)
  } >ram
  .kernel_stack : {
    *(.kernel_stack)
  } >ram
  .bss : {
    *(.bss)
  } >ram

  _end = .;

  .debug_module : {
    *(.debug_module)
  } >dm
  .dm_scratch : {
    . = ALIGN(4);
    . = . + _dm_scratch_len ;
    . = ALIGN(4);
    } >dm =0
}
