/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Machine-mode and supervisor-mode state definitions. */

/* privilege level */

register cur_privilege : Privilege

/* current instruction bits, used for illegal instruction exceptions */

register cur_inst : xlenbits

/* State projections
 *
 * Some machine state is processed via projections from machine-mode views to
 * views from lower privilege levels.  So, for e.g. when mstatus is read from
 * lower privilege levels, we use 'lowering_' projections:
 *
 *   mstatus  ->  sstatus  ->  ustatus
 *
 * Similarly, when machine state is written from lower privileges, that state is
 * lifted into the appropriate value for the machine-mode state.
 *
 *   ustatus  ->  sstatus  ->  mstatus
 *
 * In addition, several fields in machine state registers are WARL or WLRL,
 * requiring that values written to the registers be legalized.  For each such
 * register, there will be an associated 'legalize_' function.  These functions
 * will need to be supplied externally, and will depend on the legal values
 * supported by a platform/implementation (or misa).  The legalize_ functions
 * generate a legal value from the current value and the written value.  In more
 * complex cases, they will also implicitly read the current values of misa,
 * mstatus, etc.
 *
 * Each register definition below is followed by custom projections
 * and choice of legalizations if needed.  For now, we typically
 * implement the simplest legalize_ alternatives.
 */


/* M-mode registers */

bitfield Misa : xlenbits = {
  MXL  : xlen - 1 .. xlen - 2,

  Z    : 25,
  Y    : 24,
  X    : 23,
  W    : 22,
  V    : 21,
  U    : 20,
  T    : 19,
  S    : 18,
  R    : 17,
  Q    : 16,
  P    : 15,
  O    : 14,
  N    : 13,
  M    : 12,
  L    : 11,
  K    : 10,
  J    : 9,
  I    : 8,
  H    : 7,
  G    : 6,
  F    : 5,
  E    : 4,
  D    : 3,
  C    : 2,
  B    : 1,
  A    : 0
}
register misa : Misa

/* whether misa is R/W */
val sys_enable_writable_misa = {c: "sys_enable_writable_misa", ocaml: "Platform.enable_writable_misa", _: "sys_enable_writable_misa"} : unit -> bool
/* whether misa.c was enabled at boot */
val sys_enable_rvc = {c: "sys_enable_rvc", ocaml: "Platform.enable_rvc", _: "sys_enable_rvc"} : unit -> bool
/* whether misa.{f,d} were enabled at boot */
val sys_enable_fdext = {c: "sys_enable_fdext", ocaml: "Platform.enable_fdext", _: "sys_enable_fdext"} : unit -> bool
/* whether zfinx was enabled at boot */
val sys_enable_zfinx = {c: "sys_enable_zfinx", ocaml: "Platform.enable_zfinx", _: "sys_enable_zfinx"} : unit -> bool
/* whether the N extension was enabled at boot */
val sys_enable_next = {c: "sys_enable_next", ocaml: "Platform.enable_next", _: "sys_enable_next"} : unit -> bool
/* Whether FIOM bit of menvcfg/senvcfg is enabled. It must be enabled if
   supervisor mode is implemented and non-bare addressing modes are supported. */
val sys_enable_writable_fiom = {c: "sys_enable_writable_fiom", ocaml: "Platform.enable_writable_fiom", _: "sys_enable_writable_fiom"} : unit -> bool

/* How many PMP entries are implemented. This must be 0, 16 or 64 (this is checked at runtime). */
val sys_pmp_count = {c: "sys_pmp_count", ocaml: "Platform.pmp_count", _: "sys_pmp_count"} : unit -> range(0, 64)
/* G parameter that specifies the PMP grain size. The grain size is 2^(G+2), e.g.
   G=0 -> 4 bytes, G=10 -> 4096 bytes. */
val sys_pmp_grain = {c: "sys_pmp_grain", ocaml: "Platform.pmp_grain", _: "sys_pmp_grain"} : unit -> range(0, 63)

/* whether misa.v was enabled at boot */
val sys_enable_vext = {c: "sys_enable_vext", ocaml: "Platform.enable_vext", _: "sys_enable_vext"} : unit -> bool

/* This function allows an extension to veto a write to Misa
   if it would violate an alignment restriction on
   unsetting C. If it returns true the write will have no effect. */
val ext_veto_disable_C : unit -> bool

function legalize_misa(m : Misa, v : xlenbits) -> Misa = {
  let  v = Mk_Misa(v);
  /* Suppress updates to MISA if MISA is not writable or if by disabling C next PC would become misaligned or an extension vetoes */
  if   not(sys_enable_writable_misa()) | (v[C] == 0b0 & (nextPC[1] == bitone | ext_veto_disable_C()))
  then m
  else {
    /* Suppress enabling C if C was disabled at boot (i.e. not supported) */
    let m = if not(sys_enable_rvc()) then m else [m with C = v[C]];
    /* Suppress updates to misa.{f,d} if disabled at boot */
    if   not(sys_enable_fdext())
    then m
    else [m with F = v[F], D = v[D] & v[F]]
  }
}

/* helpers to check support for various extensions. */
/* we currently don't model 'E', so always assume 'I'. */
function haveAtomics() -> bool = misa[A] == 0b1
function haveRVC()     -> bool = misa[C] == 0b1
function haveMulDiv()  -> bool = misa[M] == 0b1
function haveSupMode() -> bool = misa[S] == 0b1
function haveUsrMode() -> bool = misa[U] == 0b1
function haveNExt()    -> bool = misa[N] == 0b1
/* see below for F and D (and Z*inx counterparts) extension tests */

/* BitManip extension support. */
function haveZba()  -> bool = true
function haveZbb()  -> bool = true
function haveZbc()  -> bool = true
function haveZbs()  -> bool = true

/* Zfa (additional FP) extension */
function haveZfa()  -> bool = true

/* Scalar Cryptography extensions support. */
function haveZbkb() -> bool = true
function haveZbkc() -> bool = true
function haveZbkx() -> bool = true

/* Cryptography extension support. Note these will need updating once */
/* Sail can be dynamically configured with different extension support */
/* and have dynamic changes of XLEN via S/UXL */
function haveZkr()    -> bool = true
function haveZksh()   -> bool = true
function haveZksed()  -> bool = true
function haveZknh()   -> bool = true
function haveZkne()   -> bool = true
function haveZknd()   -> bool = true

function haveZmmul()  -> bool = true

/* Zicond extension support */
function haveZicond() -> bool = true

bitfield Mstatush : bits(32) = {
  MBE  : 5,
  SBE  : 4
}
register mstatush : Mstatush

bitfield Mstatus : xlenbits = {
  SD   : xlen - 1,

  // The MBE and SBE fields are in mstatus in RV64 and absent in RV32.
  // On RV32, they are in mstatush, which doesn't exist in RV64.  For now,
  // they are handled in an ad-hoc way.
  // MBE  : 37
  // SBE  : 36

  // The SXL and UXL fields don't exist on RV32, so they are modelled
  // via explicit getters and setters; see below.
  // SXL  : 35 .. 34,
  // UXL  : 33 .. 32,

  TSR  : 22,
  TW   : 21,
  TVM  : 20,
  MXR  : 19,
  SUM  : 18,
  MPRV : 17,

  XS   : 16 .. 15,
  FS   : 14 .. 13,

  MPP  : 12 .. 11,
  VS   : 10 .. 9,
  SPP  : 8,

  MPIE : 7,
  SPIE : 5,
  UPIE : 4,

  MIE  : 3,
  SIE  : 1,
  UIE  : 0
}
register mstatus : Mstatus

function effectivePrivilege(t : AccessType(ext_access_type), m : Mstatus, priv : Privilege) -> Privilege =
  if   t != Execute() & m[MPRV] == 0b1
  then privLevel_of_bits(m[MPP])
  else priv

function get_mstatus_SXL(m : Mstatus) -> arch_xlen = {
  if   sizeof(xlen) == 32
  then arch_to_bits(RV32)
  else m.bits[35 .. 34]
}

function set_mstatus_SXL(m : Mstatus, a : arch_xlen) -> Mstatus = {
  if   sizeof(xlen) == 32
  then m
  else {
    let m = vector_update_subrange(m.bits, 35, 34,  a);
    Mk_Mstatus(m)
  }
}

function get_mstatus_UXL(m : Mstatus) -> arch_xlen = {
  if   sizeof(xlen) == 32
  then arch_to_bits(RV32)
  else m.bits[33 .. 32]
}

function set_mstatus_UXL(m : Mstatus, a : arch_xlen) -> Mstatus = {
  if   sizeof(xlen) == 32
  then m
  else {
    let m = vector_update_subrange(m.bits, 33, 32,  a);
    Mk_Mstatus(m)
  }
}

function legalize_mstatus(o : Mstatus, v : xlenbits) -> Mstatus = {
  /*
   * Populate all defined fields using the bits of v, stripping anything
   * that does not have a matching bitfield entry. All bits above 32 are handled
   * explicitly later.
   */
  let m : Mstatus = Mk_Mstatus(zero_extend(v[22 .. 7] @ 0b0 @ v[5 .. 3] @ 0b0 @ v[1 .. 0]));

  /* We don't have any extension context yet. */
  let m = [m with XS = extStatus_to_bits(Off)];

  /* FS is WARL, and making FS writable can support the M-mode emulation of an FPU
   * to support code running in S/U-modes.  Spike does this, and for now, we match it,
   * but only if Zfinx isn't enabled.
   * FIXME: This should be made a platform parameter.
   */
  let m = if sys_enable_zfinx() then [m with FS = extStatus_to_bits(Off)] else m;
  let dirty = extStatus_of_bits(m[FS]) == Dirty | extStatus_of_bits(m[XS]) == Dirty |
              extStatus_of_bits(m[VS]) == Dirty;
  let m = [m with SD = bool_to_bits(dirty)];

  /* We don't support dynamic changes to SXL and UXL. */
  let m = set_mstatus_SXL(m, get_mstatus_SXL(o));
  let m = set_mstatus_UXL(m, get_mstatus_UXL(o));

  /* We don't currently support changing MBE and SBE. */
  let m = if sizeof(xlen) == 64 then {
             Mk_Mstatus([m.bits with 37 .. 36 = 0b00])
          } else m;

  /* Hardwired to zero in the absence of 'U' or 'N'. */
  let m = if not(haveNExt()) then {
             let m = [m with UPIE = 0b0];
             let m = [m with UIE = 0b0];
             m
          } else m;

  if not(haveUsrMode()) then {
    let m = [m with MPRV = 0b0];
    m
  } else m
}

/* architecture and extension checks */

function cur_Architecture() -> Architecture = {
  let a : arch_xlen =
    match (cur_privilege) {
      Machine    => misa[MXL],
      Supervisor => get_mstatus_SXL(mstatus),
      User       => get_mstatus_UXL(mstatus)
    };
  match architecture(a) {
    Some(a) => a,
    None()  => internal_error(__FILE__, __LINE__, "Invalid current architecture")
  }
}

function in32BitMode() -> bool = {
  cur_Architecture() == RV32
}

/* F and D extensions have to enabled both via misa.{FD} as well as mstatus.FS */
function haveFExt()    -> bool = (misa[F] == 0b1) & (mstatus[FS] != 0b00)
function haveDExt()    -> bool = (misa[D] == 0b1) & (mstatus[FS] != 0b00)
/* Zfh (half-precision) extension depends on misa.F and mstatus.FS */
function haveZfh()     -> bool = (misa[F] == 0b1) & (mstatus[FS] != 0b00)
/* V extension has to enable both via misa.V as well as mstatus.VS */
function haveVExt()    -> bool = (misa[V] == 0b1) & (mstatus[VS] != 0b00)

/* Zhinx, Zfinx and Zdinx extensions (TODO: gate FCSR access on [mhs]stateen0 bit 1 when implemented) */
function haveZhinx()   -> bool = sys_enable_zfinx()
function haveZfinx()   -> bool = sys_enable_zfinx()
function haveZdinx()   -> bool = sys_enable_zfinx() & sizeof(flen) >= 64

/* interrupt processing state */

bitfield Minterrupts : xlenbits = {
  MEI : 11, /* external interrupts */
  SEI : 9,
  UEI : 8,

  MTI : 7,  /* timers interrupts */
  STI : 5,
  UTI : 4,

  MSI : 3,  /* software interrupts */
  SSI : 1,
  USI : 0,
}
register mip     : Minterrupts /* Pending */
register mie     : Minterrupts /* Enabled */
register mideleg : Minterrupts /* Delegation to S-mode */

function legalize_mip(o : Minterrupts, v : xlenbits) -> Minterrupts = {
  /* The only writable bits are the S-mode bits, and with the 'N'
   * extension, the U-mode bits. */
  let v = Mk_Minterrupts(v);
  let m = [o with SEI = v[SEI], STI = v[STI], SSI = v[SSI]];
  if haveUsrMode() & haveNExt() then {
    [m with UEI = v[UEI], UTI = v[UTI], USI = v[USI]]
  } else m
}

function legalize_mie(o : Minterrupts, v : xlenbits) -> Minterrupts = {
  let v = Mk_Minterrupts(v);
  let m = [o with
    MEI = v[MEI],
    MTI = v[MTI],
    MSI = v[MSI],
    SEI = v[SEI],
    STI = v[STI],
    SSI = v[SSI]
  ];
  /* The U-mode bits will be modified if we have the 'N' extension. */
  if haveUsrMode() & haveNExt() then {
    [m with UEI = v[UEI], UTI = v[UTI], USI = v[USI]]
  } else m
}

function legalize_mideleg(o : Minterrupts, v : xlenbits) -> Minterrupts = {
  /* M-mode interrupt delegation bits "should" be hardwired to 0. */
  /* FIXME: needs verification against eventual spec language. */
  [Mk_Minterrupts(v) with MEI = 0b0, MTI = 0b0, MSI = 0b0]
}

/* exception processing state */

bitfield Medeleg : xlenbits = {
  SAMO_Page_Fault   : 15,
  Load_Page_Fault   : 13,
  Fetch_Page_Fault  : 12,
  MEnvCall          : 10,
  SEnvCall          : 9,
  UEnvCall          : 8,
  SAMO_Access_Fault : 7,
  SAMO_Addr_Align   : 6,
  Load_Access_Fault : 5,
  Load_Addr_Align   : 4,
  Breakpoint        : 3,
  Illegal_Instr     : 2,
  Fetch_Access_Fault: 1,
  Fetch_Addr_Align  : 0
}
register medeleg : Medeleg  /* Delegation to S-mode */

function legalize_medeleg(o : Medeleg, v : xlenbits) -> Medeleg = {
  /* M-EnvCalls delegation is not supported */
  [Mk_Medeleg(v) with MEnvCall = 0b0]
}

/* registers for trap handling */

bitfield Mtvec : xlenbits = {
  Base : xlen - 1 .. 2,
  Mode : 1 .. 0
}
register mtvec : Mtvec  /* Trap Vector */

function legalize_tvec(o : Mtvec, v : xlenbits) -> Mtvec = {
 let v = Mk_Mtvec(v);
 match (trapVectorMode_of_bits(v[Mode])) {
   TV_Direct => v,
   TV_Vector => v,
   _         => [v with Mode = o[Mode]]
 }
}

bitfield Mcause : xlenbits = {
  IsInterrupt : xlen - 1,
  Cause       : xlen - 2 .. 0
}
register mcause : Mcause

/* Interpreting the trap-vector address */
function tvec_addr(m : Mtvec, c : Mcause) -> option(xlenbits) = {
  let base : xlenbits = m[Base] @ 0b00;
  match (trapVectorMode_of_bits(m[Mode])) {
    TV_Direct => Some(base),
    TV_Vector => if   c[IsInterrupt] == 0b1
                 then Some(base + (zero_extend(c[Cause]) << 2))
                 else Some(base),
    TV_Reserved => None()
  }
}

/* Exception PC */

register mepc : xlenbits

/* The xepc legalization zeroes xepc[1:0] when misa.C is hardwired to 0.
 * When misa.C is writable, it zeroes only xepc[0].
 */
function legalize_xepc(v : xlenbits) -> xlenbits =
  /* allow writing xepc[1] only if misa.C is enabled or could be enabled
     XXX specification says this legalization should be done on read */
  if   (sys_enable_writable_misa() & sys_enable_rvc()) | misa[C] == 0b1
  then [v with 0 = bitzero]
  else v & sign_extend(0b100)

/* masking for reads to xepc */
function pc_alignment_mask() -> xlenbits =
  ~(zero_extend(if misa[C] == 0b1 then 0b00 else 0b10))

/* auxiliary exception registers */

register mtval    : xlenbits
register mscratch : xlenbits

/* counters */

bitfield Counteren : bits(32) = {
  HPM  : 31 .. 3,
  IR   : 2,
  TM   : 1,
  CY   : 0
}

register mcounteren : Counteren
register scounteren : Counteren

function legalize_mcounteren(c : Counteren, v : xlenbits) -> Counteren = {
  /* no HPM counters yet */
  [c with IR = [v[2]], TM = [v[1]], CY = [v[0]]]
}

function legalize_scounteren(c : Counteren, v : xlenbits) -> Counteren = {
  /* no HPM counters yet */
  [c with IR = [v[2]], TM = [v[1]], CY = [v[0]]]
}

bitfield Counterin : bits(32) = {
  /* no HPM counters yet */
  IR : 2,
  CY : 0
}
register mcountinhibit : Counterin

function legalize_mcountinhibit(c : Counterin, v : xlenbits) -> Counterin = {
  [c with IR = [v[2]], CY = [v[0]]]
}

register mcycle : bits(64)
register mtime : bits(64)

/* minstret
 *
 * minstret is an architectural register, and can be written to.  The
 * spec says that minstret increments on instruction retires need to
 * occur before any explicit writes to instret.  However, in our
 * simulation loop, we need to execute an instruction to find out
 * whether it retired, and hence can only increment instret after
 * execution.  To avoid doing this in the case minstret was explicitly
 * written to, we track whether it should increment in a separate
 * model-internal register.
 */
register minstret : bits(64)

/* Should minstret be incremented when the instruction is retired. */
register minstret_increment : bool

function retire_instruction() -> unit = {
  if minstret_increment then minstret = minstret + 1;
}

/* informational registers */
register mvendorid : bits(32)
register mimpid : xlenbits
register marchid : xlenbits
/* TODO: this should be readonly, and always 0 for now */
register mhartid : xlenbits

/* S-mode registers */

/* sstatus reveals a subset of mstatus */
bitfield Sstatus : xlenbits = {
  SD   : xlen - 1,
  // The UXL field does not exist on RV32, so we define an explicit
  // getter and setter below.
  // UXL  : 30 .. 29,
  MXR  : 19,
  SUM  : 18,
  XS   : 16 .. 15,
  FS   : 14 .. 13,
  VS   : 10 .. 9,
  SPP  : 8,
  SPIE : 5,
  UPIE : 4,
  SIE  : 1,
  UIE  : 0
}
/* sstatus is a view of mstatus, so there is no register defined. */

function get_sstatus_UXL(s : Sstatus) -> arch_xlen = {
  let m = Mk_Mstatus(s.bits);
  get_mstatus_UXL(m)
}

function set_sstatus_UXL(s : Sstatus, a : arch_xlen) -> Sstatus = {
  let m = Mk_Mstatus(s.bits);
  let m = set_mstatus_UXL(m, a);
  Mk_Sstatus(m.bits)
}

function lower_mstatus(m : Mstatus) -> Sstatus = {
  let s = Mk_Sstatus(zero_extend(0b0));
  let s = [s with SD = m[SD]];
  let s = set_sstatus_UXL(s, get_mstatus_UXL(m));
  let s = [s with MXR = m[MXR]];
  let s = [s with SUM = m[SUM]];
  let s = [s with XS = m[XS]];
  let s = [s with FS = m[FS]];
  let s = [s with VS = m[VS]];
  let s = [s with SPP = m[SPP]];
  let s = [s with SPIE = m[SPIE]];
  let s = [s with UPIE = m[UPIE]];
  let s = [s with SIE = m[SIE]];
  let s = [s with UIE = m[UIE]];
  s
}

function lift_sstatus(m : Mstatus, s : Sstatus) -> Mstatus = {
  let m = [m with MXR = s[MXR]];
  let m = [m with SUM = s[SUM]];

  let m = [m with XS = s[XS]];
  // See comment for mstatus.FS.
  let m = [m with FS = s[FS]];
  let m = [m with VS = s[VS]];
  let dirty = extStatus_of_bits(m[FS]) == Dirty | extStatus_of_bits(m[XS]) == Dirty |
              extStatus_of_bits(m[VS]) == Dirty;
  let m = [m with SD = bool_to_bits(dirty)];

  let m = [m with SPP = s[SPP]];
  let m = [m with SPIE = s[SPIE]];
  let m = [m with UPIE = s[UPIE]];
  let m = [m with SIE = s[SIE]];
  let m = [m with UIE = s[UIE]];
  m
}

function legalize_sstatus(m : Mstatus, v : xlenbits) -> Mstatus = {
  legalize_mstatus(m, lift_sstatus(m, Mk_Sstatus(v)).bits)
}

bitfield Sedeleg : xlenbits = {
  UEnvCall          : 8,
  SAMO_Access_Fault : 7,
  SAMO_Addr_Align   : 6,
  Load_Access_Fault : 5,
  Load_Addr_Align   : 4,
  Breakpoint        : 3,
  Illegal_Instr     : 2,
  Fetch_Access_Fault: 1,
  Fetch_Addr_Align  : 0
}
register sedeleg : Sedeleg

function legalize_sedeleg(s : Sedeleg, v : xlenbits) -> Sedeleg = {
  Mk_Sedeleg(zero_extend(v[8..0]))
}

bitfield Sinterrupts : xlenbits = {
  SEI : 9,  /* external interrupts */
  UEI : 8,

  STI : 5,  /* timers interrupts */
  UTI : 4,

  SSI : 1,  /* software interrupts */
  USI : 0
}

/* Provides the sip read view of mip (m) as delegated by mideleg (d). */
function lower_mip(m : Minterrupts, d : Minterrupts) -> Sinterrupts = {
  let s : Sinterrupts = Mk_Sinterrupts(zero_extend(0b0));
  let s = [s with SEI = m[SEI] & d[SEI]];
  let s = [s with STI = m[STI] & d[STI]];
  let s = [s with SSI = m[SSI] & d[SSI]];

  let s = [s with UEI = m[UEI] & d[UEI]];
  let s = [s with UTI = m[UTI] & d[UTI]];
  let s = [s with USI = m[USI] & d[USI]];
  s
}

/* Provides the sie read view of mie (m) as delegated by mideleg (d). */
function lower_mie(m : Minterrupts, d : Minterrupts) -> Sinterrupts = {
  let s : Sinterrupts = Mk_Sinterrupts(zero_extend(0b0));
  let s = [s with SEI = m[SEI] & d[SEI]];
  let s = [s with STI = m[STI] & d[STI]];
  let s = [s with SSI = m[SSI] & d[SSI]];
  let s = [s with UEI = m[UEI] & d[UEI]];
  let s = [s with UTI = m[UTI] & d[UTI]];
  let s = [s with USI = m[USI] & d[USI]];
  s
}

/* Returns the new value of mip from the previous mip (o) and the written sip (s) as delegated by mideleg (d). */
function lift_sip(o : Minterrupts, d : Minterrupts, s : Sinterrupts) -> Minterrupts = {
  let m : Minterrupts = o;
  let m = if d[SSI] == 0b1 then [m with SSI = s[SSI]] else m;
  if haveNExt() then {
    let m = if d[UEI] == 0b1 then [m with UEI = s[UEI]] else m;
    let m = if d[USI] == 0b1 then [m with USI = s[USI]] else m;
    m
  } else m
}

function legalize_sip(m : Minterrupts, d : Minterrupts, v : xlenbits) -> Minterrupts = {
  lift_sip(m, d, Mk_Sinterrupts(v))
}

/* Returns the new value of mie from the previous mie (o) and the written sie (s) as delegated by mideleg (d). */
function lift_sie(o : Minterrupts, d : Minterrupts, s : Sinterrupts) -> Minterrupts = {
  let m : Minterrupts = o;
  let m = if d[SEI] == 0b1 then [m with SEI = s[SEI]] else m;
  let m = if d[STI] == 0b1 then [m with STI = s[STI]] else m;
  let m = if d[SSI] == 0b1 then [m with SSI = s[SSI]] else m;
  if haveNExt() then {
    let m = if d[UEI] == 0b1 then [m with UEI = s[UEI]] else m;
    let m = if d[UTI] == 0b1 then [m with UTI = s[UTI]] else m;
    let m = if d[USI] == 0b1 then [m with USI = s[USI]] else m;
    m
  } else m
}

function legalize_sie(m : Minterrupts, d : Minterrupts, v : xlenbits) -> Minterrupts = {
  lift_sie(m, d, Mk_Sinterrupts(v))
}

register sideleg : Sinterrupts

/* other non-VM related supervisor state */
register stvec    : Mtvec
register sscratch : xlenbits
register sepc     : xlenbits
register scause   : Mcause
register stval    : xlenbits

/*
 * S-mode address translation and protection (satp) layout.
 * The actual satp register is defined in an architecture-specific file.
 */

bitfield Satp64 : bits(64) = {
  Mode : 63 .. 60,
  Asid : 59 .. 44,
  PPN  : 43 .. 0
}

function legalize_satp64(a : Architecture, o : bits(64), v : bits(64)) -> bits(64) = {
  let s = Mk_Satp64(v);
  match satp64Mode_of_bits(a, s[Mode]) {
    None()     => o,
    Some(Sv32) => o,  /* Sv32 is unsupported for now */
    Some(_)    => s.bits
  }
}

bitfield Satp32 : bits(32) = {
  Mode : 31,
  Asid : 30 .. 22,
  PPN  : 21 .. 0
}

function legalize_satp32(a : Architecture, o : bits(32), v : bits(32)) -> bits(32) = {
  /* all 32-bit satp modes are valid */
  v
}

/* disabled trigger/debug module */
register tselect : xlenbits

/*
 * The seed CSR (entropy source)
 * ------------------------------------------------------------
 */

/* Valid return states for reading the seed CSR. */
enum seed_opst = {
  BIST, // Built-in-self-test. No randomness sampled.
  ES16, // Entropy-sample-16. Valid 16-bits of randomness sampled.
  WAIT, // Device still gathering entropy.
  DEAD  // Fatal device compromise. No randomness sampled.
}

/* Mapping of status codes and their actual encodings. */
mapping opst_code : seed_opst <-> bits(2) = {
  BIST <-> 0b00,
  WAIT <-> 0b01,
  ES16 <-> 0b10,
  DEAD <-> 0b11
}

/*
 * Entropy Source - Platform access to random bits.
 * WARNING: This function currently lacks a proper side-effect annotation.
 *          If you are using theorem prover tool flows, you
 *          may need to modify or stub out this function for now.
 * NOTE: This would be better placed in riscv_platform.sail, but that file
 *       appears _after_ this one in the compile order meaning the valspec
 *       for this function is unavailable when it's first encountered in
 *       read_seed_csr. Hence it appears here.
 */
val get_16_random_bits = {
    ocaml: "Platform.get_16_random_bits",
    interpreter: "Platform.get_16_random_bits",
    c: "plat_get_16_random_bits",
    lem: "plat_get_16_random_bits"
} : unit -> bits(16)

/* Entropy source spec requires an Illegal opcode exception be raised if the
 * seed register is read without also being written. This function is only
 * called once we know the CSR is being written, and all other access control
 * checks have been done.
 */
function read_seed_csr() -> xlenbits = {
  let reserved_bits : bits(6) = 0b000000;
  let custom_bits : bits(8) = 0x00;
  let seed : bits(16) = get_16_random_bits();
  zero_extend(opst_code(ES16) @ reserved_bits @ custom_bits @ seed)
}

/* Writes to the seed CSR are ignored */
function write_seed_csr () -> option(xlenbits) = None()

// menvcfg is 64 bits. senvcfg is SXLEN bits and does not have the two
// upper fields so for simplicity we can use the same type.
bitfield Envcfg : bits(64) = {
  // Supervisor TimeCmp Extension
  STCE   : 63,
  // Page Based Memory Types Extension
  PBMTE  : 62,
  // Reserved WPRI bits.
  wpri_1 : 61 .. 8,
  // Cache Block Zero instruction Enable
  CBZE   : 7,
  // Cache Block Clean and Flush instruction Enable
  CBCFE  : 6,
  // Cache Block Invalidate instruction Enable
  CBIE   : 5 .. 4,
  // Reserved WPRI bits.
  wpri_0 : 3 .. 1,
  // Fence of I/O implies Memory
  FIOM   : 0,
}

register menvcfg : Envcfg
register senvcfg : Envcfg

function legalize_envcfg(o : Envcfg, v : bits(64)) -> Envcfg = {
  let v = Mk_Envcfg(v);
  let o = [o with FIOM = if sys_enable_writable_fiom() then v[FIOM] else 0b0];
  // Other extensions are not implemented yet so all other fields are read only zero.
  o
}

// Return whether or not FIOM is currently active, based on the current
// privilege and the menvcfg/senvcfg settings. This means that I/O fences
// imply memory fence.
function is_fiom_active() -> bool = {
  match cur_privilege {
    Machine => false,
    Supervisor => menvcfg[FIOM] == 0b1,
    User => (menvcfg[FIOM] | senvcfg[FIOM]) == 0b1,
  }
}
/* vector csrs */
register vstart : bits(16) /* use the largest possible length of vstart */
register vxsat  : bits(1)
register vxrm   : bits(2)
register vl     : xlenbits
register vlenb  : xlenbits

bitfield Vtype  : xlenbits = {
  vill      : xlen - 1,
  reserved  : xlen - 2 .. 8,
  vma       : 7,
  vta       : 6,
  vsew      : 5 .. 3,
  vlmul     : 2 .. 0
}
register vtype : Vtype

/* the dynamic selected element width (SEW) */
/* this returns the power of 2 for SEW */
val get_sew_pow : unit -> {|3, 4, 5, 6|}
function get_sew_pow() = {
  let SEW_pow : {|3, 4, 5, 6|} = match vtype[vsew] {
    0b000 => 3,
    0b001 => 4,
    0b010 => 5,
    0b011 => 6,
    _     => {assert(false, "invalid vsew field in vtype"); 0}
  };
  SEW_pow
}
/* this returns the actual value of SEW */
val get_sew : unit -> {|8, 16, 32, 64|}
function get_sew() = {
  match get_sew_pow() {
    3 => 8,
    4 => 16,
    5 => 32,
    6 => 64
  }
}
/* this returns the value of SEW in bytes */
val get_sew_bytes : unit -> {1, 2, 4, 8}
function get_sew_bytes() = {
  match get_sew_pow() {
    3 => 1,
    4 => 2,
    5 => 4,
    6 => 8
  }
}

/* the vector register group multiplier (LMUL) */
/* this returns the power of 2 for LMUL */
val get_lmul_pow : unit -> range(-3, 3)
function get_lmul_pow() = {
  match vtype[vlmul] {
    0b101 => -3,
    0b110 => -2,
    0b111 => -1,
    0b000 => 0,
    0b001 => 1,
    0b010 => 2,
    0b011 => 3,
    _     => {assert(false, "invalid vlmul field in vtype"); 0}
  }
}

enum agtype = { UNDISTURBED, AGNOSTIC }

val decode_agtype : bits(1) -> agtype
function decode_agtype(ag) = {
  match ag {
    0b0 => UNDISTURBED,
    0b1 => AGNOSTIC
  }
}

val get_vtype_vma : unit -> agtype
function get_vtype_vma() = decode_agtype(vtype[vma])

val get_vtype_vta : unit -> agtype
function get_vtype_vta() = decode_agtype(vtype[vta])
