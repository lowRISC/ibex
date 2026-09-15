/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _MONO_REWRITES
$define _MONO_REWRITES

/* Definitions for use with the -mono_rewrites option */

$include <arith.sail>
$include <vector_dec.sail>

/* External definitions not in the usual asl prelude */

val extzv = pure {lem: "extz_vec"} : forall 'n 'm, 'm >= 0. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec)
function extzv(m, v) = {
  if m < 'n then truncate(v, m) else sail_zero_extend(v, m)
}

val extsv = pure {lem: "exts_vec"} : forall 'n 'm, 'm >= 0. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec)
function extsv(m, v) = {
  if m < 'n then truncate(v, m) else sail_sign_extend(v, m)
}

/* This is generated internally to deal with case splits which reveal the size
   of a bitvector */
val bitvector_cast_in = pure "zeroExtend" : forall 'n. bits('n) -> bits('n)
val bitvector_cast_out = pure "zeroExtend" : forall 'n. bits('n) -> bits('n)

/* Builtins for the rewrites */
val string_of_bits_subrange = pure "string_of_bits_subrange" : forall 'n. (bits('n), int, int) -> string

/* Definitions for the rewrites */

val is_zero_subrange : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool

function is_zero_subrange (xs, i, j) = {
  (xs & slice_mask(j, i-j+1)) == extzv([bitzero] : bits(1))
}

val is_zeros_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool

function is_zeros_slice (xs, i, l) = {
  (xs & slice_mask(i, l)) == extzv([bitzero] : bits(1))
}

val is_ones_subrange : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool

function is_ones_subrange (xs, i, j) = {
  let m : bits('n) = slice_mask(j,i-j+1) in
  (xs & m) == m
}

val is_ones_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool

function is_ones_slice (xs, i, j) = {
  let m : bits('n) = slice_mask(i,j) in
  (xs & m) == m
}

val slice_slice_concat : forall 'n 'm 'r, 'n >= 0 & 'm >= 0 & 'r >= 0.
  (implicit('r), bits('n), int, int, bits('m), int, int) -> bits('r)

function slice_slice_concat (r, xs, i, l, ys, i', l') = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  let ys = sail_shiftright(ys & slice_mask(i',l'), i') in
  sail_shiftleft(extzv(r, xs), l') | extzv(r, ys)
}

val slice_zeros_concat : forall 'n 'p 'q, 'n >= 0 & 'p + 'q >= 0.
  (bits('n), int, atom('p), atom('q)) -> bits('p + 'q)

function slice_zeros_concat (xs, i, l, l') = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  sail_shiftleft(extzv(l + l', xs), l')
}

val subrange_zeros_concat : forall 'n 'hi 'lo 'q, 'n >= 0 & 'hi - 'lo + 1 + 'q >= 0.
  (bits('n), atom('hi), atom('lo), atom('q)) -> bits('hi - 'lo + 1 + 'q)

function subrange_zeros_concat (xs, hi, lo, l') =
  slice_zeros_concat(xs, lo, hi - lo + 1, l')

/* Assumes initial vectors are of equal size */

val subrange_subrange_eq : forall 'n, 'n >= 0.
  (bits('n), int, int, bits('n), int, int) -> bool

function subrange_subrange_eq (xs, i, j, ys, i', j') = {
  let xs = sail_shiftright(xs & slice_mask(j,i-j+1), j) in
  let ys = sail_shiftright(ys & slice_mask(j',i'-j'+1), j') in
  xs == ys
}

val subrange_subrange_concat : forall 'n 'o 'p 'm 'q 'r 's, 's >= 0 & 'n >= 0 & 'm >= 0.
  (implicit('s), bits('n), atom('o), atom('p), bits('m), atom('q), atom('r)) -> bits('s)

function subrange_subrange_concat (s, xs, i, j, ys, i', j') = {
  let xs = sail_shiftright(xs & slice_mask(j,i-j+1), j) in
  let ys = sail_shiftright(ys & slice_mask(j',i'-j'+1), j') in
  sail_shiftleft(extzv(s, xs), i' - j' + 1) | extzv(s, ys)
}

val place_subrange : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int, int) -> bits('m)

function place_subrange(m,xs,i,j,shift) = {
  let xs = sail_shiftright(xs & slice_mask(j,i-j+1), j) in
  sail_shiftleft(extzv(m, xs), shift)
}

val place_slice : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int, int) -> bits('m)

function place_slice(m,xs,i,l,shift) = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  sail_shiftleft(extzv(m, xs), shift)
}

val set_slice_zeros : forall 'n, 'n >= 0.
  (implicit('n), bits('n), int, int) -> bits('n)

function set_slice_zeros(n, xs, i, l) = {
  let ys : bits('n) = slice_mask(n, i, l) in
  xs & not_vec(ys)
}

val set_subrange_zeros : forall 'n, 'n >= 0.
  (implicit('n), bits('n), int, int) -> bits('n)

function set_subrange_zeros(n, xs, hi, lo) =
  set_slice_zeros(n, xs, lo, hi - lo + 1)

val zext_slice : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int) -> bits('m)

function zext_slice(m,xs,i,l) = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  extzv(m, xs)
}

val zext_subrange : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int) -> bits('m)

function zext_subrange(m, xs, i, j) = zext_slice(m, xs, j, i - j + 1)

val sext_slice : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int) -> bits('m)

function sext_slice(m,xs,i,l) = {
  let xs = sail_arith_shiftright(sail_shiftleft((xs & slice_mask(i,l)), ('n - i - l)), 'n - l) in
  extsv(m, xs)
}

val sext_subrange : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int) -> bits('m)

function sext_subrange(m, xs, i, j) = sext_slice(m, xs, j, i - j + 1)

val place_slice_signed : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int, int) -> bits('m)

function place_slice_signed(m,xs,i,l,shift) = {
  sail_shiftleft(sext_slice(m, xs, i, l), shift)
}

val place_subrange_signed : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (implicit('m), bits('n), int, int, int) -> bits('m)

function place_subrange_signed(m,xs,i,j,shift) = {
  place_slice_signed(m, xs, j, i-j+1, shift)
}

/* This has different names in the aarch64 prelude (UInt) and the other
   preludes (unsigned).  To avoid variable name clashes, we redeclare it
   here with a suitably awkward name. */
val _builtin_unsigned = pure {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_unsigned",
  coq: "uint",
  lean: "BitVec.toNat"
} : forall 'n. bits('n) -> {'m, 0 <= 'm < 2 ^ 'n. int('m)}

/* There are different implementation choices for division and remainder, but
   they agree on positive values.  We use this here to give more precise return
   types for unsigned_slice and unsigned_subrange. */

val _builtin_mod_nat = pure {
  smt: "mod",
  ocaml: "modulus",
  lem: "integerMod",
  c: "tmod_int",
  coq: "Z.rem",
  lean: "Nat.mod"
} : forall 'n 'm, 'n >= 0 & 'm >= 0. (int('n), int('m)) -> {'r, 0 <= 'r < 'm. int('r)}

/* Below we need the fact that 2 ^ 'n >= 0, so we axiomatise it in the return
   type of pow2, as SMT solvers tend to have problems with exponentiation. */
val _builtin_pow2 = pure "pow2" : forall 'n, 'n >= 0. int('n) -> {'m, 'm == 2 ^ 'n & 'm >= 0. int('m)}

val unsigned_slice : forall 'n 'l, 'n >= 0 & 'l >= 0.
  (bits('n), int, int('l)) -> {'m, 0 <= 'm < 2 ^ 'l. int('m)}

function unsigned_slice(xs,i,l) = {
  let xs = sail_shiftright(xs & slice_mask(i,l), i) in
  _builtin_mod_nat(_builtin_unsigned(xs), _builtin_pow2(l))
}

val unsigned_subrange : forall 'n 'i 'j, 'n >= 0 & ('i - 'j) >= 0.
  (bits('n), int('i), int('j)) -> {'m, 0 <= 'm < 2 ^ ('i - 'j + 1). int('m)}

function unsigned_subrange(xs,i,j) = {
  let xs = sail_shiftright(xs & slice_mask(j,i-j+1), i) in
  _builtin_mod_nat(_builtin_unsigned(xs), _builtin_pow2(i - j + 1))
}


val zext_ones : forall 'n, 'n >= 0. (implicit('n), int) -> bits('n)

function zext_ones(n, m) = {
  let v : bits('n) = extsv([bitone] : bits(1)) in
  sail_shiftright(v, n - m)
}


val vector_update_subrange_from_subrange : forall 'n1 's1 'e1 'n2 's2 'e2,
    0 <= 'e1 <= 's1 < 'n1 & 0 <= 'e2 <= 's2 < 'n2 & 's1 - 'e1 == 's2 - 'e2.
    (implicit('n1), bits('n1), int('s1), int('e1), bits('n2), int('s2), int('e2)) -> bits('n1)

function vector_update_subrange_from_subrange(n,v1,s1,e1,v2,s2,e2) = {
  let xs = sail_shiftright(v2 & slice_mask(e2,s2-e2+1), e2) in
  let xs = sail_shiftleft(extzv(n, xs), e1) in
  let ys = v1 & not_vec(slice_mask(e1,s1-e1+1)) in
  xs | ys
}

val vector_update_subrange_from_integer_subrange : forall 'n1 's1 'e1 's2 'e2,
    0 <= 'e1 <= 's1 < 'n1 & 0 <= 'e2 <= 's2 & 's1 - 'e1 == 's2 - 'e2.
    (implicit('n1), bits('n1), int('s1), int('e1), int, int('s2), int('e2)) -> bits('n1)

function vector_update_subrange_from_integer_subrange(n1, v1, s1, e1, i, s2, e2) = {
  let v2 : bits('n1) = get_slice_int(n1, i, e2) in
  vector_update_subrange_from_subrange(n1, v1, s1, e1, v2, s2 - e2, 0)
}

$endif
