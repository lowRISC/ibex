MEMORY {
  RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 2M
}
SECTIONS {
  .text : {
  KEEP(*(.text))
  KEEP(*(.text.func))
} >RAM
  .data : {
  KEEP(*(.data))
} >RAM
  .region_0 : {
  KEEP(*(.region_0))
} >RAM
  .region_1 : {
  KEEP(*(.region_1))
} >RAM
  .user_stack 0x80080000 : {
  KEEP(*(.user_stack))
} >RAM
  .kernel_stack 0x80091000: {
  KEEP(*(.kernel_stack))
} >RAM
}
INCLUDE ./snippy/snippy_example.elf.ld
