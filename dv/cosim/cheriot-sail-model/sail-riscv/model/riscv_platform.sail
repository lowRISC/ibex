/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Platform-specific definitions, and basic MMIO devices. */

/* Current constraints on this implementation are:
   - it cannot access memory directly, but instead provides definitions for the physical memory model
   - it can access system register state, needed to manipulate interrupt bits
   - it relies on externs to get platform address information and doesn't hardcode them
*/

val elf_tohost = {
  ocaml: "Elf_loader.elf_tohost",
  interpreter: "Elf_loader.elf_tohost",
  c: "elf_tohost"
} :  unit -> int

val elf_entry = {
  ocaml: "Elf_loader.elf_entry",
  interpreter: "Elf_loader.elf_entry",
  c: "elf_entry"
} : unit -> int

/* Main memory */
val plat_ram_base = {c: "plat_ram_base", ocaml: "Platform.dram_base", interpreter: "Platform.dram_base", lem: "plat_ram_base"} : unit -> xlenbits
val plat_ram_size = {c: "plat_ram_size", ocaml: "Platform.dram_size", interpreter: "Platform.dram_size", lem: "plat_ram_size"} : unit -> xlenbits

/* whether the MMU should update dirty bits in PTEs */
val plat_enable_dirty_update = {ocaml: "Platform.enable_dirty_update",
                                interpreter: "Platform.enable_dirty_update",
                                c: "plat_enable_dirty_update",
                                lem: "plat_enable_dirty_update"} : unit -> bool

/* whether the platform supports misaligned accesses without trapping to M-mode. if false,
 * misaligned loads/stores are trapped to Machine mode.
 */
val plat_enable_misaligned_access = {ocaml: "Platform.enable_misaligned_access",
                                     interpreter: "Platform.enable_misaligned_access",
                                     c: "plat_enable_misaligned_access",
                                     lem: "plat_enable_misaligned_access"} : unit -> bool

/* whether mtval stores the bits of a faulting instruction on illegal instruction exceptions */
val plat_mtval_has_illegal_inst_bits = {ocaml: "Platform.mtval_has_illegal_inst_bits",
                                        interpreter: "Platform.mtval_has_illegal_inst_bits",
                                        c: "plat_mtval_has_illegal_inst_bits",
                                        lem: "plat_mtval_has_illegal_inst_bits"} : unit -> bool

/* ROM holding reset vector and device-tree DTB */
val plat_rom_base   = {ocaml: "Platform.rom_base", interpreter: "Platform.rom_base", c: "plat_rom_base", lem: "plat_rom_base"} : unit -> xlenbits
val plat_rom_size   = {ocaml: "Platform.rom_size", interpreter: "Platform.rom_size", c: "plat_rom_size", lem: "plat_rom_size"} : unit -> xlenbits

/* Location of clock-interface, which should match with the spec in the DTB */
val plat_clint_base = {ocaml: "Platform.clint_base", interpreter: "Platform.clint_base", c: "plat_clint_base", lem: "plat_clint_base"} : unit -> xlenbits
val plat_clint_size = {ocaml: "Platform.clint_size", interpreter: "Platform.clint_size", c: "plat_clint_size", lem: "plat_clint_size"} : unit -> xlenbits

/* Location of UART, which should match with the spec in the DTB */
val plat_uart_base = {ocaml: "Platform.uart_base", interpreter: "Platform.uart_base", c: "plat_uart_base", lem: "plat_uart_base"} : unit -> xlenbits
val plat_uart_size = {ocaml: "Platform.uart_size", interpreter: "Platform.uart_size", c: "plat_uart_size", lem: "plat_uart_size"} : unit -> xlenbits

/* Location of HTIF ports */
val plat_htif_tohost = {ocaml: "Platform.htif_tohost", c: "plat_htif_tohost", lem: "plat_htif_tohost"} : unit -> xlenbits
function plat_htif_tohost () = to_bits(sizeof(xlen), elf_tohost ())
// todo: fromhost

val phys_mem_segments : unit -> list((xlenbits, xlenbits))
function phys_mem_segments() =
  (plat_rom_base (), plat_rom_size ()) ::
  (plat_ram_base (), plat_ram_size ()) ::
  [||]

/* Physical memory map predicates */

function within_phys_mem forall 'n, 'n <= max_mem_access. (addr : xlenbits, width : atom('n)) -> bool = {
  /* To avoid overflow issues when physical memory extends to the end
   * of the addressable range, we need to perform address bound checks
   * on unsigned unbounded integers.
   */
  let addr_int     = unsigned(addr);
  let ram_base_int = unsigned(plat_ram_base ());
  let rom_base_int = unsigned(plat_rom_base ());
  let ram_size_int = unsigned(plat_ram_size ());
  let rom_size_int = unsigned(plat_rom_size ());

  /* todo: iterate over segment list */
  if      (  ram_base_int <= addr_int
           & (addr_int + sizeof('n)) <= (ram_base_int + ram_size_int))
  then    true
  else if (  rom_base_int <= addr_int
           & (addr_int + sizeof('n)) <= (rom_base_int + rom_size_int))
  then    true
  else {
    print_platform("within_phys_mem: " ^ BitStr(addr) ^ " not within phys-mem:");
    print_platform("  plat_rom_base: " ^ BitStr(plat_rom_base ()));
    print_platform("  plat_rom_size: " ^ BitStr(plat_rom_size ()));
    print_platform("  plat_ram_base: " ^ BitStr(plat_ram_base ()));
    print_platform("  plat_ram_size: " ^ BitStr(plat_ram_size ()));
    false
  }
}

function within_clint forall 'n, 0 < 'n <= max_mem_access . (addr : xlenbits, width : atom('n)) -> bool = {
  /* To avoid overflow issues when physical memory extends to the end
   * of the addressable range, we need to perform address bound checks
   * on unsigned unbounded integers.
   */
  let addr_int       = unsigned(addr);
  let clint_base_int = unsigned(plat_clint_base ());
  let clint_size_int = unsigned(plat_clint_size ());
    clint_base_int <= addr_int
  & (addr_int + sizeof('n)) <= (clint_base_int + clint_size_int)
}

function within_htif_writable forall 'n, 0 < 'n <= max_mem_access . (addr : xlenbits, width : atom('n)) -> bool =
    plat_htif_tohost() == addr | (plat_htif_tohost() + 4 == addr & width == 4)

function within_htif_readable forall 'n, 0 < 'n <= max_mem_access . (addr : xlenbits, width : atom('n)) -> bool =
    plat_htif_tohost() == addr | (plat_htif_tohost() + 4 == addr & width == 4)

function within_uart forall 'n, 0 < 'n <= max_mem_access . (addr : xlenbits, width : atom('n)) -> bool = {
  /* To avoid overflow issues when physical memory extends to the end
   * of the addressable range, we need to perform address bound checks
   * on unsigned unbounded integers.
   */
  let addr_int      = unsigned(addr);
  let uart_base_int = unsigned(plat_uart_base());
  let uart_size_int = unsigned(plat_uart_size());
    uart_base_int <= addr_int
  & (addr_int + sizeof('n)) <= (uart_base_int + uart_size_int)
}

/* CLINT (Core Local Interruptor), based on Spike. */

val plat_insns_per_tick = {ocaml: "Platform.insns_per_tick", interpreter: "Platform.insns_per_tick", c: "plat_insns_per_tick", lem: "plat_insns_per_tick"} : unit -> int

// assumes a single hart, since this typically is a vector of per-hart registers.
register mtimecmp : bits(64)  // memory-mapped internal clint register.

/* CLINT memory-mapped IO */

/* relative address map:
 *
 * 0000 msip hart 0         -- memory-mapped software interrupt
 * 0004 msip hart 1
 * 4000 mtimecmp hart 0 lo  -- memory-mapped timer thresholds
 * 4004 mtimecmp hart 0 hi
 * 4008 mtimecmp hart 1 lo
 * 400c mtimecmp hart 1 hi
 * bff8 mtime lo            -- memory-mapped clocktimer value
 * bffc mtime hi
 */

let MSIP_BASE        : xlenbits = zero_extend(0x00000)
let MTIMECMP_BASE    : xlenbits = zero_extend(0x04000)
let MTIMECMP_BASE_HI : xlenbits = zero_extend(0x04004)
let MTIME_BASE       : xlenbits = zero_extend(0x0bff8)
let MTIME_BASE_HI    : xlenbits = zero_extend(0x0bffc)

val clint_load : forall 'n, 'n > 0. (AccessType(ext_access_type), xlenbits, int('n)) -> MemoryOpResult(bits(8 * 'n))
function clint_load(t, addr, width) = {
  let addr = addr - plat_clint_base ();
  /* FIXME: For now, only allow exact aligned access. */
  if addr == MSIP_BASE & ('n == 8 | 'n == 4)
  then {
    if   get_config_print_platform()
    then print_platform("clint[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mip[MSI]));
    MemValue(sail_zero_extend(mip[MSI], sizeof(8 * 'n)))
  }
  else if addr == MTIMECMP_BASE & ('n == 4)
  then {
    if   get_config_print_platform()
    then print_platform("clint<4>[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mtimecmp[31..0]));
    /* FIXME: Redundant zero_extend currently required by Lem backend */
    MemValue(sail_zero_extend(mtimecmp[31..0], 32))
  }
  else if addr == MTIMECMP_BASE & ('n == 8)
  then {
    if   get_config_print_platform()
    then print_platform("clint<8>[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mtimecmp));
    /* FIXME: Redundant zero_extend currently required by Lem backend */
    MemValue(sail_zero_extend(mtimecmp, 64))
  }
  else if addr == MTIMECMP_BASE_HI & ('n == 4)
  then {
    if   get_config_print_platform()
    then print_platform("clint-hi<4>[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mtimecmp[63..32]));
    /* FIXME: Redundant zero_extend currently required by Lem backend */
    MemValue(sail_zero_extend(mtimecmp[63..32], 32))
  }
  else if addr == MTIME_BASE & ('n == 4)
  then {
    if   get_config_print_platform()
    then print_platform("clint[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mtime));
    MemValue(sail_zero_extend(mtime[31..0], 32))
  }
  else if addr == MTIME_BASE & ('n == 8)
  then {
    if   get_config_print_platform()
    then print_platform("clint[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mtime));
    MemValue(sail_zero_extend(mtime, 64))
  }
  else if addr == MTIME_BASE_HI & ('n == 4)
  then {
    if   get_config_print_platform()
    then print_platform("clint[" ^ BitStr(addr) ^ "] -> " ^ BitStr(mtime));
    MemValue(sail_zero_extend(mtime[63..32], 32))
  }
  else {
    if   get_config_print_platform()
    then print_platform("clint[" ^ BitStr(addr) ^ "] -> <not-mapped>");
    match t {
      Execute()  => MemException(E_Fetch_Access_Fault()),
      Read(Data) => MemException(E_Load_Access_Fault()),
      _          => MemException(E_SAMO_Access_Fault())
    }
  }
}

function clint_dispatch() -> unit = {
  if   get_config_print_platform()
  then print_platform("clint::tick mtime <- " ^ BitStr(mtime));
  mip[MTI] = 0b0;
  if mtimecmp <=_u mtime then {
    if   get_config_print_platform()
    then print_platform(" clint timer pending at mtime " ^ BitStr(mtime));
    mip[MTI] = 0b1
  }
}

/* The rreg effect is due to checking mtime. */
val clint_store: forall 'n, 'n > 0. (xlenbits, int('n), bits(8 * 'n)) -> MemoryOpResult(bool)
function clint_store(addr, width, data) = {
  let addr = addr - plat_clint_base ();
  if addr == MSIP_BASE & ('n == 8 | 'n == 4) then {
    if   get_config_print_platform()
    then print_platform("clint[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data) ^ " (mip.MSI <- " ^ BitStr(data[0]) ^ ")");
    mip[MSI] = [data[0]];
    clint_dispatch();
    MemValue(true)
  } else if addr == MTIMECMP_BASE & 'n == 8 then {
    if   get_config_print_platform()
    then print_platform("clint<8>[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data) ^ " (mtimecmp)");
    mtimecmp = sail_zero_extend(data, 64); /* FIXME: Redundant zero_extend currently required by Lem backend */
    clint_dispatch();
    MemValue(true)
  } else if addr == MTIMECMP_BASE & 'n == 4 then {
    if   get_config_print_platform()
    then print_platform("clint<4>[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data) ^ " (mtimecmp)");
    mtimecmp = vector_update_subrange(mtimecmp, 31, 0, sail_zero_extend(data, 32));  /* FIXME: Redundant zero_extend currently required by Lem backend */
    clint_dispatch();
    MemValue(true)
  } else if addr == MTIMECMP_BASE_HI & 'n == 4 then {
    if   get_config_print_platform()
    then print_platform("clint<4>[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data) ^ " (mtimecmp)");
    mtimecmp = vector_update_subrange(mtimecmp, 63, 32, sail_zero_extend(data, 32)); /* FIXME: Redundant zero_extend currently required by Lem backend */
    clint_dispatch();
    MemValue(true)
  } else {
    if   get_config_print_platform()
    then print_platform("clint[" ^ BitStr(addr) ^ "] <- " ^ BitStr(data) ^ " (<unmapped>)");
    MemException(E_SAMO_Access_Fault())
  }
}

val tick_clock : unit -> unit
function tick_clock() = {
  if   mcountinhibit[CY] == 0b0
  then mcycle = mcycle + 1;

  mtime  = mtime  + 1;
  clint_dispatch()
}

/* Basic terminal character I/O. */

val plat_term_write = {ocaml: "Platform.term_write", c: "plat_term_write", lem: "plat_term_write"} : bits(8) -> unit
val plat_term_read  = {ocaml: "Platform.term_read",  c: "plat_term_read", lem: "plat_term_read"}  : unit -> bits(8)

/* Spike's HTIF device interface, which multiplexes the above MMIO devices. */

bitfield htif_cmd : bits(64) = {
  device  : 63 .. 56,
  cmd     : 55 .. 48,
  payload : 47 .. 0
}

register htif_tohost : bits(64)
register htif_done   : bool
register htif_exit_code : bits(64)

/* Applications sometimes write the lower 32-bit payload bytes without
   writing the control bytes; this is seen in the riscv-tests suite.
   However, processing the payload bytes too early could miss a
   subsequent write to the control bytes.  As a workaround, if the
   payload is written a few times with the same value, without an
   intervening write to the control bytes, we process the whole htif
   command anyway.  */

register htif_cmd_write : bit
register htif_payload_writes : bits(4)

/* Once a htif command has been processed, the port is reset. */
function reset_htif () -> unit = {
  htif_cmd_write = bitzero;
  htif_payload_writes = 0x0;
  htif_tohost = zero_extend(0b0);
}

/* Since the htif tohost port is only available at a single address,
 * we'll assume here that physical memory model has correctly
 * dispatched the address.
 */

val htif_load : forall 'n, 'n > 0. (AccessType(ext_access_type), xlenbits, int('n)) -> MemoryOpResult(bits(8 * 'n))
function htif_load(t, paddr, width) = {
  if   get_config_print_platform()
  then print_platform("htif[" ^ BitStr(paddr) ^ "] -> " ^ BitStr(htif_tohost));
  /* FIXME: For now, only allow the expected access widths. */
  if      width == 8 & (paddr == plat_htif_tohost())
  then    MemValue(sail_zero_extend(htif_tohost, 64))         /* FIXME: Redundant zero_extend currently required by Lem backend */
  else if width == 4 & paddr == plat_htif_tohost()
  then    MemValue(sail_zero_extend(htif_tohost[31..0], 32))  /* FIXME: Redundant zero_extend currently required by Lem backend */
  else if width == 4 & paddr == plat_htif_tohost() + 4
  then    MemValue(sail_zero_extend(htif_tohost[63..32], 32)) /* FIXME: Redundant zero_extend currently required by Lem backend */
  else match t {
    Execute()  => MemException(E_Fetch_Access_Fault()),
    Read(Data) => MemException(E_Load_Access_Fault()),
    _          => MemException(E_SAMO_Access_Fault())
  }
}

/* The rreg,wreg effects are an artifact of using 'register' to implement device state. */
val htif_store: forall 'n, 0 < 'n <= 8. (xlenbits, int('n), bits(8 * 'n)) -> MemoryOpResult(bool)
function htif_store(paddr, width, data) = {
  if   get_config_print_platform()
  then print_platform("htif[" ^ BitStr(paddr) ^ "] <- " ^ BitStr(data));
  /* Store the written value so that we can ack it later. */
  if      width == 8
  then    { htif_cmd_write = bitone;
            htif_payload_writes = htif_payload_writes + 1;
            htif_tohost = zero_extend(data) }
  else if width == 4 & paddr == plat_htif_tohost()
  then    { if   data == htif_tohost[31 .. 0]
            then htif_payload_writes = htif_payload_writes + 1
            else htif_payload_writes = 0x1;
            htif_tohost = vector_update_subrange(htif_tohost, 31, 0, data) }
  else if width == 4 & paddr == plat_htif_tohost() + 4
  then    { if   data[15 .. 0] == htif_tohost[47 .. 32]
            then htif_payload_writes = htif_payload_writes + 1
            else htif_payload_writes = 0x1;
            htif_cmd_write = bitone;
            htif_tohost = vector_update_subrange(htif_tohost, 63, 32, data) }
  /* unaligned command writes are not supported and will not be detected */
  else    { htif_tohost = zero_extend(data) };

  /* Execute if there were repeated writes of the same payload without
   * a cmd (e.g. in riscv-tests), or we have a complete htif command.
   */
  if   (((htif_cmd_write == bitone) & (unsigned(htif_payload_writes) > 0))
        | (unsigned(htif_payload_writes) > 2))
  then {
    let cmd = Mk_htif_cmd(htif_tohost);
    match cmd[device] {
      0x00 => { /* syscall-proxy */
        if   get_config_print_platform()
        then print_platform("htif-syscall-proxy cmd: " ^ BitStr(cmd[payload]));
        if   cmd[payload][0] == bitone
        then {
             htif_done = true;
             htif_exit_code = (sail_zero_extend(cmd[payload], 64) >> 1)
        }
        else ()
      },
      0x01 => { /* terminal */
        if   get_config_print_platform()
        then print_platform("htif-term cmd: " ^ BitStr(cmd[payload]));
        match cmd[cmd] {
          0x00 => /* TODO: terminal input handling */ (),
          0x01 => plat_term_write(cmd[payload][7..0]),
          c    => print("Unknown term cmd: " ^ BitStr(c))
        };
        /* reset to ack */
        reset_htif()
      },
      d => print("htif-???? cmd: " ^ BitStr(data))
    }
  };
  MemValue(true)
}

val htif_tick : unit -> unit
function htif_tick() = {
  if   get_config_print_platform()
  then print_platform("htif::tick " ^ BitStr(htif_tohost));
  htif_tohost = htif_tohost /* prevent this function being optimized out */
}

/* Top-level MMIO dispatch */
$ifndef RVFI_DII
function within_mmio_readable forall 'n, 0 < 'n <= max_mem_access . (addr : xlenbits, width : atom('n)) -> bool =
  within_uart (addr, width) | within_clint(addr, width) | (within_htif_readable(addr, width) & 1 <= 'n)
$else
function within_mmio_readable forall 'n, 0 < 'n <= max_mem_access . (addr : xlenbits, width : atom('n)) -> bool =
  within_clint(addr, width)
$endif

$ifndef RVFI_DII
function within_mmio_writable forall 'n, 0 < 'n <= max_mem_access . (addr : xlenbits, width : atom('n)) -> bool =
  within_uart (addr, width) | within_clint(addr, width) | (within_htif_writable(addr, width) & 'n <= 8)
$else
function within_mmio_writable forall 'n, 0 < 'n <= max_mem_access . (addr : xlenbits, width : atom('n)) -> bool =
  within_clint(addr, width)
$endif

/* This is a very minimal UART implementation: just enough to allow a basic
driver to output to the console. It ignores the configuration registers and
does not supporting reading except from the line status register which indictes
it is always ready to transmit. Does not support interrupts. */

let UART_OFFSET_DATA    = 0x00000000
let UART_OFFSET_LINE_CTL = 0x0000000c
let UART_OFFSET_LINE_STATUS = 0x00000014
/* Divisor latch access bit. We need this so that we can ignore writes to data
  register while the driver programs the baud rate (otherwise we might print
  garbage on console). */
register UART_DLAB : bit = bitzero

val uart_load : forall 'n, 'n > 0. (AccessType(ext_access_type), xlenbits, int('n)) -> MemoryOpResult(bits(8 * 'n))
function uart_load(t, addr, width) = {
  let offset = addr - plat_uart_base();
  /* We only support reading the status register, which always indicates ready to write output */
  if offset == zero_extend(UART_OFFSET_LINE_STATUS) & ('n == 4)
  then {
    let result = 0b100000; /* TXBufEmpty always */
    if   get_config_print_platform()
    then print_platform("uart[" ^ BitStr(offset) ^ "] -> " ^ BitStr(result));
    MemValue(sail_zero_extend(result, sizeof(8 * 'n)))
  } else {
    if   get_config_print_platform()
    then print_platform("uart[" ^ BitStr(offset) ^ "] -> <not-mapped>");
    match t {
      Execute()  => MemException(E_Fetch_Access_Fault()),
      Read(Data) => MemException(E_Load_Access_Fault()),
      _          => MemException(E_SAMO_Access_Fault())
    }
  }
}

val uart_store: forall 'n, 'n > 0. (xlenbits, int('n), bits(8 * 'n)) -> MemoryOpResult(bool)
function uart_store(addr, width, data) = {
  let offset = addr - plat_uart_base();
  /* only support writing to the data register for output, ignore other writes */
  if offset == zero_extend(UART_OFFSET_DATA) & ('n == 8 | 'n == 4) then {
    if   get_config_print_platform()
    then print_platform("uart[" ^ BitStr(offset) ^ "] <- " ^ BitStr(data));
    if UART_DLAB == bitzero then plat_term_write(data[7..0]);
    MemValue(true)
  } else if offset == zero_extend(UART_OFFSET_LINE_CTL) & ('n == 8 | 'n == 4) then {
    if   get_config_print_platform()
    then print_platform("uart[" ^ BitStr(offset) ^ "] <- " ^ BitStr(data));
    UART_DLAB = data[7];
    MemValue(true)
  } else {
    if   get_config_print_platform()
    then print_platform("uart[" ^ BitStr(offset) ^ "] <- " ^ BitStr(data) ^ " (<ignored>)");
    MemValue(true)
  }
}

function mmio_read forall 'n, 0 < 'n <= max_mem_access . (t : AccessType(ext_access_type), paddr : xlenbits, width : atom('n)) -> MemoryOpResult(bits(8 * 'n)) =
  if   within_uart(paddr, width)
  then uart_load(t, paddr, width)
  else if within_clint(paddr, width)
  then clint_load(t, paddr, width)
  else if within_htif_readable(paddr, width) & (1 <= 'n)
  then htif_load(t, paddr, width)
  else match t {
    Execute()  => MemException(E_Fetch_Access_Fault()),
    Read(Data) => MemException(E_Load_Access_Fault()),
    _          => MemException(E_SAMO_Access_Fault())
  }

function mmio_write forall 'n, 0 <'n <= max_mem_access . (paddr : xlenbits, width : atom('n), data: bits(8 * 'n)) -> MemoryOpResult(bool) =
  if   within_uart(paddr, width)
  then uart_store(paddr, width, data)
  else if within_clint(paddr, width)
  then clint_store(paddr, width, data)
  else if within_htif_writable(paddr, width) & 'n <= 8
  then htif_store(paddr, width, data)
  else MemException(E_SAMO_Access_Fault())

/* Platform initialization and ticking. */

function init_platform() -> unit = {
  htif_tohost = zero_extend(0b0);
  htif_done   = false;
  htif_exit_code = zero_extend(0b0);
  htif_cmd_write = bitzero;
  htif_payload_writes = zero_extend(0b0);
}

function tick_platform() -> unit = {
  htif_tick();
}

/* Platform-specific handling of instruction faults */

function handle_illegal() -> unit = {
  let info = if plat_mtval_has_illegal_inst_bits ()
             then Some(instbits)
             else None();
  let t : sync_exception = struct { trap    = E_Illegal_Instr(),
                                    excinfo = info,
                                    ext     = None() };
  set_next_pc(exception_handler(cur_privilege, CTL_TRAP(t), PC))
}

/* Platform-specific wait-for-interrupt */

function platform_wfi() -> unit = {
  cancel_reservation();
  /* speed execution by getting the timer to fire at the next instruction,
   * since we currently don't have any other devices raising interrupts.
   */
  if mtime <_u mtimecmp then {
    mtime  = mtimecmp;
    mcycle = mtimecmp;
  }
}
