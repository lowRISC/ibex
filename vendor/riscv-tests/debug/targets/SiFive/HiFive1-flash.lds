OUTPUT_ARCH( "riscv" )

MEMORY
{
    flash (rxl) : ORIGIN = 0x20400000, LENGTH = 128K
    ram (wx) : ORIGIN = 0x80000000, LENGTH = 16K
}

SECTIONS
{
  flash_text : {
    *(.text.entry)
    *(.text)
  } >flash

  /* data segment */
  .data : { *(.data) } >ram

  .sdata : {
    __global_pointer$ = . + 0x800;
    *(.srodata.cst16) *(.srodata.cst8) *(.srodata.cst4) *(.srodata.cst2)
    *(.srodata*)
    *(.sdata .sdata.* .gnu.linkonce.s.*)
  } >ram

  /* bss segment */
  __bss_start = .;
  .sbss : {
    *(.sbss .sbss.* .gnu.linkonce.sb.*)
    *(.scommon)
  } >ram
  .bss : { *(.bss) } >ram
  __bss_end = .;

  __malloc_start = .;
  . = . + 512;

  /* End of uninitalized data segement */
  _end = .;
}

ENTRY(_start)

ASSERT(_end < 0x80004000, "program is too large")
