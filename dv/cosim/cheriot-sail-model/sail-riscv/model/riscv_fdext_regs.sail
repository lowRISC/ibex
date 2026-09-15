/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* **************************************************************** */
/* Floating point register file and accessors for F, D extensions   */
/* Floating point CSR and accessors                                 */
/* **************************************************************** */

/* Original version written by Rishiyur S. Nikhil, Sept-Oct 2019    */

/* **************************************************************** */
/* NaN boxing/unboxing.                                             */
/* When 16-bit floats (half-precision) are stored in 32/64-bit regs  */
/* they must be 'NaN boxed'.                                         */
/* When 16-bit floats (half-precision) are read from 32/64-bit regs  */
/* they must be 'NaN unboxed'.                                       */
/* When 32-bit floats (single-precision) are stored in 64-bit regs  */
/* they must be 'NaN boxed' (upper 32b all ones).                   */
/* When 32-bit floats (single-precision) are read from 64-bit regs  */
/* they must be 'NaN unboxed'.                                      */

function canonical_NaN_H() -> bits(16) = 0x_7e00
function canonical_NaN_S() -> bits(32) = 0x_7fc0_0000
function canonical_NaN_D() -> bits(64) = 0x_7ff8_0000_0000_0000

val      nan_box_H : bits(16) -> flenbits
function nan_box_H   val_16b =
  if (sizeof(flen) == 32)
  then 0x_FFFF @ val_16b
  else 0x_FFFF_FFFF_FFFF @ val_16b

val      nan_unbox_H : flenbits -> bits(16)
function nan_unbox_H   regval =
  if (sizeof(flen) == 32)
  then if regval [32..16] == 0x_FFFF
       then regval [15..0]
       else canonical_NaN_H()
  else if regval [63..16] == 0x_FFFF_FFFF_FFFF
       then regval [15..0]
       else canonical_NaN_H()

val nan_box_S : bits(32) -> flenbits
function nan_box_S val_32b = {
  assert(sys_enable_fdext());
  if (sizeof(flen) == 32)
  then val_32b
  else 0x_FFFF_FFFF @ val_32b
}

val nan_unbox_S : flenbits -> bits(32)
function nan_unbox_S regval = {
  assert(sys_enable_fdext());
  if (sizeof(flen) == 32)
  then regval
  else if regval [63..32] == 0x_FFFF_FFFF
       then regval [31..0]
       else canonical_NaN_S()
}

overload nan_box = { nan_box_H, nan_box_S }
overload nan_unbox = { nan_unbox_H, nan_unbox_S }

/* **************************************************************** */
/* Floating point register file                                     */

register f0  : fregtype
register f1  : fregtype
register f2  : fregtype
register f3  : fregtype
register f4  : fregtype
register f5  : fregtype
register f6  : fregtype
register f7  : fregtype
register f8  : fregtype
register f9  : fregtype
register f10 : fregtype
register f11 : fregtype
register f12 : fregtype
register f13 : fregtype
register f14 : fregtype
register f15 : fregtype
register f16 : fregtype
register f17 : fregtype
register f18 : fregtype
register f19 : fregtype
register f20 : fregtype
register f21 : fregtype
register f22 : fregtype
register f23 : fregtype
register f24 : fregtype
register f25 : fregtype
register f26 : fregtype
register f27 : fregtype
register f28 : fregtype
register f29 : fregtype
register f30 : fregtype
register f31 : fregtype

function dirty_fd_context() -> unit = {
  assert(sys_enable_fdext());
  mstatus[FS] = extStatus_to_bits(Dirty);
  mstatus[SD] = 0b1
}

function dirty_fd_context_if_present() -> unit = {
  assert(sys_enable_fdext() != sys_enable_zfinx());
  if sys_enable_fdext() then dirty_fd_context()
}

val rF : forall 'n, 0 <= 'n < 32. regno('n) -> flenbits
function rF r = {
  assert(sys_enable_fdext());
  let v : fregtype =
    match r {
      0 => f0,
      1 => f1,
      2 => f2,
      3 => f3,
      4 => f4,
      5 => f5,
      6 => f6,
      7 => f7,
      8 => f8,
      9 => f9,
      10 => f10,
      11 => f11,
      12 => f12,
      13 => f13,
      14 => f14,
      15 => f15,
      16 => f16,
      17 => f17,
      18 => f18,
      19 => f19,
      20 => f20,
      21 => f21,
      22 => f22,
      23 => f23,
      24 => f24,
      25 => f25,
      26 => f26,
      27 => f27,
      28 => f28,
      29 => f29,
      30 => f30,
      31 => f31,
      _  => {assert(false, "invalid floating point register number"); zero_freg}
    };
  fregval_from_freg(v)
}

val wF : forall 'n, 0 <= 'n < 32. (regno('n), flenbits) -> unit
function wF (r, in_v) = {
  assert(sys_enable_fdext());
  let v = fregval_into_freg(in_v);
  match r {
    0  => f0 = v,
    1  => f1 = v,
    2  => f2 = v,
    3  => f3 = v,
    4  => f4 = v,
    5  => f5 = v,
    6  => f6 = v,
    7  => f7 = v,
    8  => f8 = v,
    9  => f9 = v,
    10 => f10 = v,
    11 => f11 = v,
    12 => f12 = v,
    13 => f13 = v,
    14 => f14 = v,
    15 => f15 = v,
    16 => f16 = v,
    17 => f17 = v,
    18 => f18 = v,
    19 => f19 = v,
    20 => f20 = v,
    21 => f21 = v,
    22 => f22 = v,
    23 => f23 = v,
    24 => f24 = v,
    25 => f25 = v,
    26 => f26 = v,
    27 => f27 = v,
    28 => f28 = v,
    29 => f29 = v,
    30 => f30 = v,
    31 => f31 = v,
    _  => assert(false, "invalid floating point register number")
  };

  dirty_fd_context();

  if   get_config_print_reg()
  then
      /* TODO: will only print bits; should we print in floating point format? */
      print_reg("f" ^ dec_str(r) ^ " <- " ^ FRegStr(v));
}

function rF_bits(i: bits(5)) -> flenbits = rF(unsigned(i))

function wF_bits(i: bits(5), data: flenbits) -> unit = {
  wF(unsigned(i)) = data
}

overload F = {rF_bits, wF_bits, rF, wF}

val rF_H : bits(5) -> bits(16)
function rF_H(i) = {
  assert(sizeof(flen) >= 16);
  assert(sys_enable_fdext() & not(sys_enable_zfinx()));
  nan_unbox(F(i))
}

val wF_H : (bits(5), bits(16)) -> unit
function wF_H(i, data) = {
  assert(sizeof(flen) >= 16);
  assert(sys_enable_fdext() & not(sys_enable_zfinx()));
  F(i) = nan_box(data)
}

val rF_S : bits(5) -> bits(32)
function rF_S(i) = {
  assert(sizeof(flen) >= 32);
  assert(sys_enable_fdext() & not(sys_enable_zfinx()));
  nan_unbox(F(i))
}

val wF_S : (bits(5), bits(32)) -> unit
function wF_S(i, data) = {
  assert(sizeof(flen) >= 32);
  assert(sys_enable_fdext() & not(sys_enable_zfinx()));
  F(i) = nan_box(data)
}

val rF_D : bits(5) -> bits(64)
function rF_D(i) = {
  assert(sizeof(flen) >= 64);
  assert(sys_enable_fdext() & not(sys_enable_zfinx()));
  F(i)
}

val wF_D : (bits(5), bits(64)) -> unit
function wF_D(i, data) = {
  assert(sizeof(flen) >= 64);
  assert(sys_enable_fdext() & not(sys_enable_zfinx()));
  F(i) = data
}

overload F_H = { rF_H, wF_H }
overload F_S = { rF_S, wF_S }
overload F_D = { rF_D, wF_D }

val rF_or_X_H : bits(5) -> bits(16)
function rF_or_X_H(i) = {
  assert(sizeof(flen) >= 16);
  assert(sys_enable_fdext() != sys_enable_zfinx());
  if   sys_enable_fdext()
  then F_H(i)
  else X(i, rs_na)[15..0]
}

val rF_or_X_S : bits(5) -> bits(32)
function rF_or_X_S(i) = {
  assert(sizeof(flen) >= 32);
  assert(sys_enable_fdext() != sys_enable_zfinx());
  if   sys_enable_fdext()
  then F_S(i)
  else X(i, rs_na)[31..0]
}

val rF_or_X_D : bits(5) -> bits(64)
function rF_or_X_D(i) = {
  assert(sizeof(flen) >= 64);
  assert(sys_enable_fdext() != sys_enable_zfinx());
  if   sys_enable_fdext()
  then F_D(i)
  else if sizeof(xlen) >= 64
  then X(i, rs_na)[63..0]
  else {
    assert(i[0] == bitzero);
    if i == zeros() then zeros() else X(i + 1) @ X(i, rs_na)
  }
}

val wF_or_X_H : (bits(5), bits(16)) -> unit
function wF_or_X_H(i, data) = {
  assert(sizeof(flen) >= 16);
  assert(sys_enable_fdext() != sys_enable_zfinx());
  if   sys_enable_fdext()
  then F_H(i) = data
  else X(i, rs_na) = sign_extend(data)
}

val wF_or_X_S : (bits(5), bits(32)) -> unit
function wF_or_X_S(i, data) = {
  assert(sizeof(flen) >= 32);
  assert(sys_enable_fdext() != sys_enable_zfinx());
  if   sys_enable_fdext()
  then F_S(i) = data
  else X(i, rs_na) = sign_extend(data)
}

val wF_or_X_D : (bits(5), bits(64)) -> unit
function wF_or_X_D(i, data) = {
  assert (sizeof(flen) >= 64);
  assert(sys_enable_fdext() != sys_enable_zfinx());
  if   sys_enable_fdext()
  then F_D(i) = data
  else if sizeof(xlen) >= 64
  then X(i, rs_na) = sign_extend(data)
  else {
    assert (i[0] == bitzero);
    if i != zeros() then {
      X(i, rs_na)     = data[31..0];
      X(i + 1) = data[63..32];
    }
  }
}

overload F_or_X_H = { rF_or_X_H, wF_or_X_H }
overload F_or_X_S = { rF_or_X_S, wF_or_X_S }
overload F_or_X_D = { rF_or_X_D, wF_or_X_D }

/* register names */

val freg_name_abi : regidx <-> string

mapping freg_name_abi = {
    0b00000 <-> "ft0",
    0b00001 <-> "ft1",
    0b00010 <-> "ft2",
    0b00011 <-> "ft3",
    0b00100 <-> "ft4",
    0b00101 <-> "ft5",
    0b00110 <-> "ft6",
    0b00111 <-> "ft7",
    0b01000 <-> "fs0",
    0b01001 <-> "fs1",
    0b01010 <-> "fa0",
    0b01011 <-> "fa1",
    0b01100 <-> "fa2",
    0b01101 <-> "fa3",
    0b01110 <-> "fa4",
    0b01111 <-> "fa5",
    0b10000 <-> "fa6",
    0b10001 <-> "fa7",
    0b10010 <-> "fs2",
    0b10011 <-> "fs3",
    0b10100 <-> "fs4",
    0b10101 <-> "fs5",
    0b10110 <-> "fs6",
    0b10111 <-> "fs7",
    0b11000 <-> "fs8",
    0b11001 <-> "fs9",
    0b11010 <-> "fs10",
    0b11011 <-> "fs11",
    0b11100 <-> "ft8",
    0b11101 <-> "ft9",
    0b11110 <-> "ft10",
    0b11111 <-> "ft11"
}

overload to_str = {freg_name_abi}

/* mappings for assembly */

val freg_name : bits(5) <-> string
mapping freg_name = {
    0b00000 <-> "ft0",
    0b00001 <-> "ft1",
    0b00010 <-> "ft2",
    0b00011 <-> "ft3",
    0b00100 <-> "ft4",
    0b00101 <-> "ft5",
    0b00110 <-> "ft6",
    0b00111 <-> "ft7",
    0b01000 <-> "fs0",
    0b01001 <-> "fs1",
    0b01010 <-> "fa0",
    0b01011 <-> "fa1",
    0b01100 <-> "fa2",
    0b01101 <-> "fa3",
    0b01110 <-> "fa4",
    0b01111 <-> "fa5",
    0b10000 <-> "fa6",
    0b10001 <-> "fa7",
    0b10010 <-> "fs2",
    0b10011 <-> "fs3",
    0b10100 <-> "fs4",
    0b10101 <-> "fs5",
    0b10110 <-> "fs6",
    0b10111 <-> "fs7",
    0b11000 <-> "fs8",
    0b11001 <-> "fs9",
    0b11010 <-> "fs10",
    0b11011 <-> "fs11",
    0b11100 <-> "ft8",
    0b11101 <-> "ft9",
    0b11110 <-> "ft10",
    0b11111 <-> "ft11"
}

val freg_or_reg_name : bits(5) <-> string
mapping freg_or_reg_name = {
  reg if sys_enable_fdext() <-> freg_name(reg) if sys_enable_fdext(),
  reg if sys_enable_zfinx() <-> reg_name(reg)  if sys_enable_zfinx()
}

val init_fdext_regs : unit -> unit
function init_fdext_regs () = {
  f0  = zero_freg;
  f1  = zero_freg;
  f2  = zero_freg;
  f3  = zero_freg;
  f4  = zero_freg;
  f5  = zero_freg;
  f6  = zero_freg;
  f7  = zero_freg;
  f8  = zero_freg;
  f9  = zero_freg;
  f10 = zero_freg;
  f11 = zero_freg;
  f12 = zero_freg;
  f13 = zero_freg;
  f14 = zero_freg;
  f15 = zero_freg;
  f16 = zero_freg;
  f17 = zero_freg;
  f18 = zero_freg;
  f19 = zero_freg;
  f20 = zero_freg;
  f21 = zero_freg;
  f22 = zero_freg;
  f23 = zero_freg;
  f24 = zero_freg;
  f25 = zero_freg;
  f26 = zero_freg;
  f27 = zero_freg;
  f28 = zero_freg;
  f29 = zero_freg;
  f30 = zero_freg;
  f31 = zero_freg
}

/* **************************************************************** */
/* Floating Point CSR                                               */
/*     fflags    address 0x001    same as fcrs [4..0]               */
/*     frm       address 0x002    same as fcrs [7..5]               */
/*     fcsr      address 0x003                                      */


bitfield Fcsr : bits(32) = {
  FRM    : 7 .. 5,
  FFLAGS : 4 .. 0,
}

register fcsr : Fcsr

val ext_write_fcsr : (bits(3), bits(5)) -> unit
function ext_write_fcsr (frm, fflags) = {
  fcsr[FRM]    = frm;      /* Note: frm can be an illegal value, 101, 110, 111 */
  fcsr[FFLAGS] = fflags;
  dirty_fd_context_if_present();
}

/* OR flags into the fflags register. */
val accrue_fflags : (bits(5)) -> unit
function accrue_fflags(flags) = {
  let f = fcsr[FFLAGS] | flags;
  if  fcsr[FFLAGS] != f
  then {
    fcsr[FFLAGS] = f;
    dirty_fd_context_if_present();
  }
}
