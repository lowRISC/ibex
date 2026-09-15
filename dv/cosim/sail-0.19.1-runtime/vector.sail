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

$ifndef _VECTOR
$define _VECTOR

$ifndef _DEFAULT_ORDER_SET
$include_error A default order must be set (using `default Order dec` or `default Order inc`) before including this file
$endif

$include <flow.sail>
$include <arith.sail>

type bits('n) = bitvector('n)

val eq_bits = pure {
  ocaml: "eq_list",
  interpreter: "eq_list",
  lem: "eq_vec",
  coq: "eq_vec",
  lean: "_lean_beq",
  _: "eq_bits"
} : forall 'n. (bits('n), bits('n)) -> bool

overload operator == = {eq_bit, eq_bits}

val neq_bits = pure {
  lem: "neq_vec",
  coq: "neq_vec",
  c: "neq_bits",
  lean: "_lean_bne"
} : forall 'n. (bits('n), bits('n)) -> bool

function neq_bits(x, y) = not_bool(eq_bits(x, y))

overload operator != = {neq_bits}

val bitvector_length = pure {
  coq: "length_mword",
  lean: "Sail.BitVec.length",
  _: "length"
} : forall 'n. bits('n) -> int('n)

val vector_length = pure {
  ocaml: "length",
  interpreter: "length",
  lem: "length_list",
  coq: "vec_length",
  lean: "Vector.length",
  _: "length"
} : forall 'n ('a : Type). vector('n, 'a) -> int('n)

val vector_init = pure {
  lean: "vectorInit",
  _: "vector_init"
} : forall 'n ('a : Type), 'n >= 0. (implicit('n), 'a) -> vector('n, 'a)

overload length = {bitvector_length, vector_length}

val count_leading_zeros = pure {
  lean: "BitVec.countLeadingZeros",
  _: "count_leading_zeros"
} : forall 'N , 'N >= 1. bits('N) -> {'n, 0 <= 'n <= 'N . atom('n)}

val count_trailing_zeros = pure {
  lean: "BitVec.countTrailingZeros",
  _: "count_trailing_zeros"
} : forall 'N , 'N >= 1. bits('N) -> {'n, 0 <= 'n <= 'N . atom('n)}

$ifndef PRINT_EFFECTS

$[sv_module { stdout = true }]
val print_bits = pure "print_bits" : forall 'n. (string, bits('n)) -> unit

$[sv_module { stderr = true }]
val prerr_bits = pure "prerr_bits" : forall 'n. (string, bits('n)) -> unit

$else

val print_bits = impure "print_bits_effect" : forall 'n. (string, bits('n)) -> unit

val prerr_bits = impure "prerr_bits_effect" : forall 'n. (string, bits('n)) -> unit

$endif

val sail_sign_extend = pure {
  lean: "Sail.BitVec.signExtend",
  _: "sign_extend"
} : forall 'n 'm, 'm >= 'n. (bits('n), int('m)) -> bits('m)

val sail_zero_extend = pure {
  lean: "Sail.BitVec.zeroExtend",
  _: "zero_extend"
} : forall 'n 'm, 'm >= 'n. (bits('n), int('m)) -> bits('m)

/*!
THIS`(v, n)` truncates `v`, keeping only the _least_ significant `n` bits.
 */
val truncate = pure {
  ocaml: "vector_truncate",
  interpreter: "vector_truncate",
  lem: "vector_truncate",
  coq: "vector_truncate",
  lean: "Sail.BitVec.truncate",
  _: "sail_truncate"
} : forall 'm 'n, 'm >= 0 & 'm <= 'n. (bits('n), int('m)) -> bits('m)

/*!
THIS`(v, n)` truncates `v`, keeping only the _most_ significant `n` bits.
 */
val truncateLSB = pure {
  ocaml: "vector_truncateLSB",
  interpreter: "vector_truncateLSB",
  lem: "vector_truncateLSB",
  coq: "vector_truncateLSB",
  lean: "Sail.BitVec.truncateLsb",
  _: "sail_truncateLSB"
} : forall 'm 'n, 'm >= 0 & 'm <= 'n. (bits('n), int('m)) -> bits('m)

val sail_mask : forall 'len 'v, 'len >= 0 & 'v >= 0. (int('len), bits('v)) -> bits('len)

function sail_mask(len, v) = if len <= length(v) then truncate(v, len) else sail_zero_extend(v, len)

overload operator ^ = {sail_mask}

val bitvector_concat = pure {
  ocaml: "append",
  interpreter: "append",
  lem: "concat_vec",
  coq: "concat_vec",
  lean: "_lean_app",
   _: "append"
} : forall 'n 'm.
  (bits('n), bits('m)) -> bits('n + 'm)

overload append = {bitvector_concat}

/* Used for creating long bitvector literals in the C backend. */
val append_64 = pure "append_64" : forall 'n. (bits('n), bits(64)) -> bits('n + 64)

$ifdef _DEFAULT_DEC
val bitvector_access = pure {
  ocaml: "access",
  interpreter: "access",
  lem: "access_vec_dec",
  coq: "access_vec_dec",
  lean: "BitVec.access",
  _: "vector_access"
} : forall ('n : Int) ('m : Int), 0 <= 'm < 'n . (bits('n), int('m)) -> bit
$else
val bitvector_access = pure {
  ocaml: "access_inc",
  interpreter: "access_inc",
  lem: "access_vec_inc",
  coq: "access_vec_inc",
  lean: "BitVec.accessBE",
  _: "vector_access_inc"
} : forall ('n : Int) ('m : Int), 0 <= 'm < 'n . (bits('n), int('m)) -> bit
$endif

val plain_vector_access = pure {
  ocaml: "access",
  interpreter: "access",
  lem: "access_list_dec",
  coq: "vec_access_dec",
  lean: "GetElem?.getElem!",
  _: "vector_access"
} : forall ('n : Int) ('m : Int) ('a : Type), 0 <= 'm < 'n. (vector('n, dec, 'a), int('m)) -> 'a

overload vector_access = {bitvector_access, plain_vector_access}

$ifdef _DEFAULT_DEC
val bitvector_update = pure {
  ocaml: "update",
  interpreter: "update",
  lem: "update_vec_dec",
  coq: "update_vec_dec",
  lean: "BitVec.update",
  _: "vector_update"
} : forall 'n 'm, 0 <= 'm < 'n. (bits('n), int('m), bit) -> bits('n)
$else
val bitvector_update = pure {
  ocaml: "update_inc",
  interpreter: "update_inc",
  lem: "update_vec_inc",
  coq: "update_vec_inc",
  lean: "BitVec.updateBE",
  _: "vector_update_inc"
} : forall 'n 'm, 0 <= 'm < 'n. (bits('n), int('m), bit) -> bits('n)
$endif

val plain_vector_update = pure {
  ocaml: "update",
  interpreter: "update",
  lem: "update_list_dec",
  coq: "vec_update_dec",
  lean: "vectorUpdate",
  _: "vector_update"
} : forall 'n 'm ('a : Type), 0 <= 'm < 'n. (vector('n, dec, 'a), int('m), 'a) -> vector('n, dec, 'a)

overload vector_update = {bitvector_update, plain_vector_update}

val add_bits = pure {
  ocaml: "add_vec",
  interpreter: "add_vec",
  lem: "add_vec",
  coq: "add_vec",
  lean: "_lean_add",
  _: "add_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_bits_int = pure {
  ocaml: "add_vec_int",
  interpreter: "add_vec_int",
  lem: "add_vec_int",
  coq: "add_vec_int",
  lean: "BitVec.addInt",
  _: "add_bits_int"
} : forall 'n. (bits('n), int) -> bits('n)

overload operator + = {add_bits, add_bits_int}

val sub_bits = pure {
  ocaml: "sub_vec",
  interpreter: "sub_vec",
  lem: "sub_vec",
  coq: "sub_vec",
  lean: "_lean_sub",
  _: "sub_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

val not_vec = pure {
  ocaml: "not_vec",
  lem: "not_vec",
  coq: "not_vec",
  interpreter: "not_vec",
  lean: "Complement.complement",
  _: "not_bits"
} : forall 'n. bits('n) -> bits('n)

val and_vec = pure {
  lem: "and_vec",
  coq: "and_vec",
  ocaml: "and_vec",
  interpreter: "and_vec",
  lean: "_lean_bvand",
  _: "and_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

overload operator & = {and_vec}

val or_vec = pure {
  lem: "or_vec",
  coq: "or_vec",
  ocaml: "or_vec",
  interpreter: "or_vec",
  lean: "_lean_bvor",
  _: "or_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

overload operator | = {or_vec}

val xor_vec = pure {
  lem: "xor_vec",
  coq: "xor_vec",
  ocaml: "xor_vec",
  interpreter: "xor_vec",
  lean: "_lean_bvxor",
  _: "xor_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

$ifdef _DEFAULT_DEC
val subrange_bits = pure {
  ocaml: "subrange",
  interpreter: "subrange",
  lem: "subrange_vec_dec",
  coq: "subrange_vec_dec",
  lean: "Sail.BitVec.extractLsb",
  _: "vector_subrange"
} : forall ('n : Int) ('m : Int) ('o : Int), 0 <= 'o <= 'm < 'n.
  (bits('n), int('m), int('o)) -> bits('m - 'o + 1)
$else
val subrange_bits = pure {
  ocaml: "subrange_inc",
  interpreter: "subrange_inc",
  lem: "subrange_vec_inc",
  coq: "subrange_vec_inc",
  lean: "BitVec.subrangeBE",
  _: "vector_subrange_inc"
} : forall ('n : Int) ('m : Int) ('o : Int), 0 <= 'm <= 'o < 'n.
  (bits('n), int('m), int('o)) -> bits('o - 'm + 1)
$endif

overload vector_subrange = {subrange_bits}

$ifdef _DEFAULT_DEC
val update_subrange_bits = pure {
  ocaml: "update_subrange",
  interpreter: "update_subrange",
  lem: "update_subrange_vec_dec",
  coq: "update_subrange_vec_dec",
  lean: "Sail.BitVec.updateSubrange",
  _: "vector_update_subrange"
} : forall 'n 'm 'o, 0 <= 'o <= 'm < 'n. (bits('n), int('m), int('o), bits('m - ('o - 1))) -> bits('n)
$else
val update_subrange_bits = pure {
  ocaml: "update_subrange_inc",
  interpreter: "update_subrange_inc",
  lem: "update_subrange_vec_inc",
  coq: "update_subrange_vec_inc",
  lean: "Sail.BitVec.updateSubrangeBE",
  _: "vector_update_subrange_inc"
} : forall 'n 'm 'o, 0 <= 'm <= 'o < 'n. (bits('n), int('m), int('o), bits('o - ('m - 1))) -> bits('n)
$endif

overload vector_update_subrange = {update_subrange_bits}

val sail_shiftleft = pure {
  lean: "_lean_shiftl",
  _: "shiftl"} : forall 'n ('ord : Order).
    (bitvector('n, 'ord), int) -> bitvector('n, 'ord)

val sail_shiftright = pure {
  lean: "_lean_shiftr",
  _: "shiftr"} : forall 'n ('ord : Order).
    (bitvector('n, 'ord), int) -> bitvector('n, 'ord)

val sail_arith_shiftright = pure {
  lean: "BitVec.rotateRight",
  _: "arith_shiftr"} : forall 'n ('ord : Order).
    (bitvector('n, 'ord), int) -> bitvector('n, 'ord)

val sail_zeros = pure {
  lean: "BitVec.zero",
  _: "zeros" }: forall 'n, 'n >= 0. int('n) -> bits('n)

val sail_ones : forall 'n, 'n >= 0. int('n) -> bits('n)

function sail_ones(n) = not_vec(sail_zeros(n))

// Some ARM specific builtins

$ifdef _DEFAULT_DEC
val slice = pure {
  lean: "BitVec.slice",
  _: "slice"} : forall 'n 'm 'o, 0 <= 'm & 0 <= 'n.
  (bits('m), int('o), int('n)) -> bits('n)
$else
val slice = pure {
  lean: "BitVec.sliceBE",
  _: "slice_inc"} : forall 'n 'm 'o, 0 <= 'o < 'm & 'o + 'n <= 'm.
  (bits('m), int('o), int('n)) -> bits('n)
$endif

val replicate_bits = pure {
  lean: "BitVec.replicateBits",
  _: "replicate_bits" } : forall 'n 'm, 'm >= 0. (bits('n), int('m)) -> bits('n * 'm)

val slice_mask : forall 'n, 'n >= 0. (implicit('n), int, int) -> bits('n)
function slice_mask(n,i,l) =
  if l >= n then {
    sail_shiftleft(sail_ones(n), i)
  } else {
    let one : bits('n) = sail_mask(n, [bitone] : bits(1)) in
    sail_shiftleft(sub_bits(sail_shiftleft(one, l), one), i)
  }

val get_slice_int = pure "get_slice_int" : forall 'w. (int('w), int, int) -> bits('w)

val set_slice_int = pure "set_slice_int" : forall 'w. (int('w), int, int, bits('w)) -> int

val set_slice_bits = pure "set_slice" : forall 'n 'm.
  (implicit('n), int('m), bits('n), int, bits('m)) -> bits('n)

$ifndef NO_SIGNED_UNSIGNED

/*!
converts a bit vector of length $n$ to an integer in the range $0$ to $2^n - 1$.
 */
val unsigned = pure {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  coq: "uint",
  lean: "BitVec.toNat",
  _: "sail_unsigned"
} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)

/* We need a non-empty vector so that the range makes sense */
/*!
converts a bit vector of length $n$ to an integer in the range $-2^{n-1}$ to $2^{n-1} - 1$ using twos-complement.
 */
val signed = pure {
  ocaml: "sint",
  lem: "sint",
  interpreter: "sint",
  coq: "sint",
  lean: "BitVec.toInt",
  _: "sail_signed"
} : forall 'n, 'n > 0. bits('n) -> range(- (2 ^ ('n - 1)), 2 ^ ('n - 1) - 1)

$endif

overload __size = {__id, bitvector_length, vector_length}

// Little endian bytes conversion, least significant byte ends up at index 0 in the vector
val to_bytes_le : forall 'n, 'n > 0. (implicit('n), bits (8 * 'n)) -> vector('n, bits(8))

$ifdef _DEFAULT_DEC
function to_bytes_le(n, b) = {
    var res = vector_init(n, sail_zeros(8));
    foreach (i from 0 to (n - 1)) {
        res[i] = b[(8 * i + 7) .. (8 * i)]
    };
    res
}
$else
function to_bytes_le(n, b) = {
    var res = vector_init(n, sail_zeros(8));
    foreach (i from 0 to (n - 1)) {
        res[i] = b[(8 * (n - 1 - i)) .. (8 * (n - 1 - i) + 7)]
    };
    res
}
$endif

val from_bytes_le : forall 'n, 'n > 0. (implicit('n), vector('n, bits(8))) -> bits(8 * 'n)

$ifdef _DEFAULT_DEC
function from_bytes_le(n, v) = {
    var res = sail_zeros(8 * n);
    foreach (i from 0 to (n - 1)) {
        res[(8 * i + 7) .. (8 * i)] = v[i]
    };
    res
}
$else
function from_bytes_le(n, v) = {
    var res = sail_zeros(8 * n);
    foreach (i from 0 to (n - 1)) {
        res[(8 * (n - 1 - i)) .. (8 * (n - 1 - i) + 7)] = v[i]
    };
    res
}
$endif

$endif
