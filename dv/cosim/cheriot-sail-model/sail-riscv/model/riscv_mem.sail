/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Physical memory model.
 *
 * This assumes that the platform memory map has been defined, so that accesses
 * to MMIO regions can be dispatched.
 *
 * The implementation below supports the reading and writing of memory
 * metadata in addition to raw memory data.
 *
 * The external API for this module is composed of three central functions
 *
 *   mem_read_priv_meta
 *   mem_write_ea
 *   mem_write_value_priv_meta
 *
 * and some special cases which partially apply these functions:
 *
 *   mem_read_priv - strips metadata from reads
 *   mem_read_meta - uses effectivePrivilege
 *   mem_read      - both of the above partial applications
 *
 *   mem_write_value_meta - uses effectivePrivilege
 *   mem_write_value_priv - uses a default value for metadata
 *   mem_write_value      - both of the above partial applications
 *
 * The internal implementation first performs a PMP check (if PMP is
 * enabled), and then dispatches to MMIO regions or physical memory as
 * per the platform memory map.
 */

function is_aligned_addr forall 'n. (addr : xlenbits, width : atom('n)) -> bool =
  unsigned(addr) % width == 0

function read_kind_of_flags (aq : bool, rl : bool, res : bool) -> option(read_kind) =
  match (aq, rl, res) {
    (false, false, false) => Some(Read_plain),
    (true, false, false)  => Some(Read_RISCV_acquire),
    (true, true, false)   => Some(Read_RISCV_strong_acquire),
    (false, false, true)  => Some(Read_RISCV_reserved),
    (true, false, true)   => Some(Read_RISCV_reserved_acquire),
    (true, true, true)    => Some(Read_RISCV_reserved_strong_acquire),
    (false, true, false)  => None(), /* should these be instead throwing error_not_implemented as below? */
    (false, true, true)   => None()
  }

// only used for actual memory regions, to avoid MMIO effects
function phys_mem_read forall 'n, 0 < 'n <= max_mem_access . (t : AccessType(ext_access_type), paddr : xlenbits, width : atom('n), aq : bool, rl: bool, res : bool, meta : bool) -> MemoryOpResult((bits(8 * 'n), mem_meta)) = {
  let result = (match read_kind_of_flags(aq, rl, res) {
    Some(rk) => Some(read_ram(rk, paddr, width, meta)),
    None()   => None()
  }) : option((bits(8 * 'n), mem_meta));
  match (t, result) {
    (Execute(),  None()) => MemException(E_Fetch_Access_Fault()),
    (Read(Data), None()) => MemException(E_Load_Access_Fault()),
    (_,          None()) => MemException(E_SAMO_Access_Fault()),
    (_,      Some(v, m)) => { if   get_config_print_mem()
                              then print_mem("mem[" ^ to_str(t) ^ "," ^ BitStr(paddr) ^ "] -> " ^ BitStr(v));
                              MemValue(v, m) }
  }
}

/* dispatches to MMIO regions or physical memory regions depending on physical memory map */
function checked_mem_read forall 'n, 0 < 'n <= max_mem_access . (t : AccessType(ext_access_type), paddr : xlenbits, width : atom('n), aq : bool, rl : bool, res: bool, meta : bool) -> MemoryOpResult((bits(8 * 'n), mem_meta)) =
  if   within_mmio_readable(paddr, width)
  then MemoryOpResult_add_meta(mmio_read(t, paddr, width), default_meta)
  else if within_phys_mem(paddr, width)
  then match ext_check_phys_mem_read(t, paddr, width, aq, rl, res, meta) {
    Ext_PhysAddr_OK()     => phys_mem_read(t, paddr, width, aq, rl, res, meta),
    Ext_PhysAddr_Error(e) => MemException(e)
  } else match t {
    Execute()  => MemException(E_Fetch_Access_Fault()),
    Read(Data) => MemException(E_Load_Access_Fault()),
    _          => MemException(E_SAMO_Access_Fault())
  }

/* PMP checks if enabled */
function pmp_mem_read forall 'n, 0 < 'n <= max_mem_access . (t : AccessType(ext_access_type), p : Privilege, paddr : xlenbits, width : atom('n), aq : bool, rl : bool, res: bool, meta : bool) -> MemoryOpResult((bits(8 * 'n), mem_meta)) =
  if   sys_pmp_count() == 0
  then checked_mem_read(t, paddr, width, aq, rl, res, meta)
  else {
    match pmpCheck(paddr, width, t, p) {
      None()  => checked_mem_read(t, paddr, width, aq, rl, res, meta),
      Some(e) => MemException(e)
    }
  }

/* Atomic accesses can be done to MMIO regions, e.g. in kernel access to device registers. */

$ifdef RVFI_DII
val rvfi_read : forall 'n, 'n > 0. (xlenbits, atom('n), MemoryOpResult((bits(8 * 'n), mem_meta))) -> unit
function rvfi_read (addr, width, result) = {
  rvfi_mem_data[rvfi_mem_addr] = zero_extend(addr);
  rvfi_mem_data_present = true;
  match result {
    /* TODO: report tag bit for capability writes and extend mask by one bit. */
    MemValue(v, _) => if width <= 16
                       then { rvfi_mem_data[rvfi_mem_rdata] = sail_zero_extend(v, 256);
                              rvfi_mem_data[rvfi_mem_rmask] = rvfi_encode_width_mask(width) }
                       else { internal_error(__FILE__, __LINE__, "Expected at most 16 bytes here!") },
    MemException(_) => ()
  };
}
$else
val rvfi_read : forall 'n, 'n > 0. (xlenbits, atom('n), MemoryOpResult((bits(8 * 'n), mem_meta))) -> unit
function rvfi_read (addr, width, result) = ()
$endif

/* NOTE: The rreg effect is due to MMIO. */
$ifdef RVFI_DII
val mem_read      : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), xlenbits, atom('n), bool, bool, bool)       -> MemoryOpResult(bits(8 * 'n))
val mem_read_priv : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), Privilege, xlenbits, atom('n), bool, bool, bool)       -> MemoryOpResult(bits(8 * 'n))
val mem_read_meta : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), xlenbits, atom('n), bool, bool, bool, bool) -> MemoryOpResult((bits(8 * 'n), mem_meta))
val mem_read_priv_meta : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), Privilege, xlenbits, atom('n), bool, bool, bool, bool) -> MemoryOpResult((bits(8 * 'n), mem_meta))
$else
val mem_read      : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), xlenbits, atom('n), bool, bool, bool)       -> MemoryOpResult(bits(8 * 'n))
val mem_read_priv : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), Privilege, xlenbits, atom('n), bool, bool, bool)       -> MemoryOpResult(bits(8 * 'n))
val mem_read_meta : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), xlenbits, atom('n), bool, bool, bool, bool) -> MemoryOpResult((bits(8 * 'n), mem_meta))
val mem_read_priv_meta : forall 'n, 0 < 'n <= max_mem_access . (AccessType(ext_access_type), Privilege, xlenbits, atom('n), bool, bool, bool, bool) -> MemoryOpResult((bits(8 * 'n), mem_meta))
$endif

/* The most generic memory read operation */
function mem_read_priv_meta (typ, priv, paddr, width, aq, rl, res, meta) = {
  let result : MemoryOpResult((bits(8 * 'n), mem_meta)) =
    if (aq | res) & not(is_aligned_addr(paddr, width))
    then MemException(E_Load_Addr_Align())
    else match (aq, rl, res) {
      (false, true,  false) => throw(Error_not_implemented("load.rl")),
      (false, true,  true)  => throw(Error_not_implemented("lr.rl")),
      (_, _, _)             => pmp_mem_read(typ, priv, paddr, width, aq, rl, res, meta)
    };
  rvfi_read(paddr, width, result);
  result
}

function mem_read_meta (typ, paddr, width, aq, rl, res, meta) =
  mem_read_priv_meta(typ, effectivePrivilege(typ, mstatus, cur_privilege), paddr, width, aq, rl, res, meta)

/* Specialized mem_read_meta that drops the metadata */
function mem_read_priv (typ, priv, paddr, width, aq, rl, res) =
  MemoryOpResult_drop_meta(mem_read_priv_meta(typ, priv, paddr, width, aq, rl, res, false))

/* Specialized mem_read_priv that operates at the default effective privilege */
function mem_read (typ, paddr, width, aq, rel, res) =
  mem_read_priv(typ, effectivePrivilege(typ, mstatus, cur_privilege), paddr, width, aq, rel, res)

val mem_write_ea : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, atom('n), bool, bool, bool) -> MemoryOpResult(unit)

function mem_write_ea (addr, width, aq, rl, con) = {
  if (rl | con) & not(is_aligned_addr(addr, width))
  then MemException(E_SAMO_Addr_Align())
  else match (aq, rl, con) {
    (false, false, false) => MemValue(write_ram_ea(Write_plain, addr, width)),
    (false, true,  false) => MemValue(write_ram_ea(Write_RISCV_release, addr, width)),
    (false, false, true)  => MemValue(write_ram_ea(Write_RISCV_conditional, addr, width)),
    (false, true , true)  => MemValue(write_ram_ea(Write_RISCV_conditional_release, addr, width)),
    (true,  false, false) => throw(Error_not_implemented("store.aq")),
    (true,  true,  false) => MemValue(write_ram_ea(Write_RISCV_strong_release, addr, width)),
    (true,  false, true)  => throw(Error_not_implemented("sc.aq")),
    (true,  true , true)  => MemValue(write_ram_ea(Write_RISCV_conditional_strong_release, addr, width))
  }
}

$ifdef RVFI_DII
val rvfi_write : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, atom('n), bits(8 * 'n), mem_meta, MemoryOpResult(bool)) -> unit
function rvfi_write (addr, width, value, meta, result) = {
  rvfi_mem_data[rvfi_mem_addr] = zero_extend(addr);
  rvfi_mem_data_present = true;
  match result {
    /* Log only the memory address (without the value) if the write fails. */
    MemValue(_) => if width <= 16 then {
        /* TODO: report tag bit for capability writes and extend mask by one bit. */
        rvfi_mem_data[rvfi_mem_wdata] = sail_zero_extend(value,256);
        rvfi_mem_data[rvfi_mem_wmask] = rvfi_encode_width_mask(width);
      } else {
        internal_error(__FILE__, __LINE__, "Expected at most 16 bytes here!");
      },
    MemException(_) => ()
  }
}
$else
val rvfi_write : forall 'n, 'n > 0. (xlenbits, atom('n), bits(8 * 'n), mem_meta, MemoryOpResult(bool)) -> unit
function rvfi_write (addr, width, value, meta, result) = ()
$endif

// only used for actual memory regions, to avoid MMIO effects
function phys_mem_write forall 'n, 0 < 'n <= max_mem_access . (wk : write_kind, paddr : xlenbits, width : atom('n), data : bits(8 * 'n), meta : mem_meta) -> MemoryOpResult(bool) = {
  let result = MemValue(write_ram(wk, paddr, width, data, meta));
  if   get_config_print_mem()
  then print_mem("mem[" ^ BitStr(paddr) ^ "] <- " ^ BitStr(data));
  result
}

/* dispatches to MMIO regions or physical memory regions depending on physical memory map */
function checked_mem_write forall 'n, 0 < 'n <= max_mem_access . (wk : write_kind, paddr : xlenbits, width : atom('n), data: bits(8 * 'n), meta: mem_meta) -> MemoryOpResult(bool) =
  if   within_mmio_writable(paddr, width)
  then mmio_write(paddr, width, data)
  else if within_phys_mem(paddr, width)
  then match ext_check_phys_mem_write (wk, paddr, width, data, meta) {
    Ext_PhysAddr_OK() => phys_mem_write(wk, paddr, width, data, meta),
    Ext_PhysAddr_Error(e)  => MemException(e)
  }
  else MemException(E_SAMO_Access_Fault())

/* PMP checks if enabled */
function pmp_mem_write forall 'n, 0 < 'n <= max_mem_access . (wk: write_kind, paddr : xlenbits, width : atom('n), data: bits(8 * 'n), typ: AccessType(ext_access_type), priv: Privilege, meta: mem_meta) -> MemoryOpResult(bool) =
  if   sys_pmp_count() == 0
  then checked_mem_write(wk, paddr, width, data, meta)
  else {
    match pmpCheck(paddr, width, typ, priv) {
      None()  => checked_mem_write(wk, paddr, width, data, meta),
      Some(e) => MemException(e)
    }
  }

/* Atomic accesses can be done to MMIO regions, e.g. in kernel access to device registers. */

/* Memory write with an explicit metadata value.  Metadata writes are
 * currently assumed to have the same alignment constraints as their
 * data.
 * NOTE: The wreg effect is due to MMIO, the rreg is due to checking mtime.
 */
val mem_write_value_priv_meta : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, atom('n), bits(8 * 'n), AccessType(ext_access_type), Privilege, mem_meta, bool, bool, bool) -> MemoryOpResult(bool)
function mem_write_value_priv_meta (paddr, width, value, typ, priv, meta, aq, rl, con) = {
  if (rl | con) & not(is_aligned_addr(paddr, width))
  then MemException(E_SAMO_Addr_Align())
  else {
    let wk : write_kind = match (aq, rl, con) {
      (false, false, false) => Write_plain,
      (false, true,  false) => Write_RISCV_release,
      (false, false, true)  => Write_RISCV_conditional,
      (false, true , true)  => Write_RISCV_conditional_release,
      (true,  true,  false) => Write_RISCV_strong_release,
      (true,  true , true)  => Write_RISCV_conditional_strong_release,
      // throw an illegal instruction here?
      (true,  false, false) => throw(Error_not_implemented("store.aq")),
      (true,  false, true)  => throw(Error_not_implemented("sc.aq"))
    };
    let result = pmp_mem_write(wk, paddr, width, value, typ, priv, meta);
    rvfi_write(paddr, width, value, meta, result);
    result
  }
}

/* Memory write with explicit Privilege, implicit AccessType and metadata */
val mem_write_value_priv : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, atom('n), bits(8 * 'n), Privilege, bool, bool, bool) -> MemoryOpResult(bool)
function mem_write_value_priv (paddr, width, value, priv, aq, rl, con) =
  mem_write_value_priv_meta(paddr, width, value, Write(default_write_acc), priv, default_meta, aq, rl, con)

/* Memory write with explicit metadata and AccessType, implicit and Privilege */
val mem_write_value_meta : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, atom('n), bits(8 * 'n), ext_access_type, mem_meta, bool, bool, bool) -> MemoryOpResult(bool)
function mem_write_value_meta (paddr, width, value, ext_acc, meta, aq, rl, con) = {
  let typ = Write(ext_acc);
  let ep = effectivePrivilege(typ, mstatus, cur_privilege);
  mem_write_value_priv_meta(paddr, width, value, typ, ep, meta, aq, rl, con)
}

/* Memory write with default AccessType, Privilege, and metadata */
val mem_write_value : forall 'n, 0 < 'n <= max_mem_access . (xlenbits, atom('n), bits(8 * 'n), bool, bool, bool) -> MemoryOpResult(bool)
function mem_write_value (paddr, width, value, aq, rl, con) = {
  mem_write_value_meta(paddr, width, value, default_write_acc, default_meta, aq, rl, con)
}
