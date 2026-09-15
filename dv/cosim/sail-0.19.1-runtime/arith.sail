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

$ifndef _ARITH
$define _ARITH

$include <flow.sail>

// ***** Addition *****

val add_atom = pure {ocaml: "add_int", interpreter: "add_int", lem: "integerAdd", coq: "Z.add", lean: "_lean_addi", _: "add_int"} : forall 'n 'm.
  (int('n), int('m)) -> int('n + 'm)

val add_int = pure {ocaml: "add_int", interpreter: "add_int", lem: "integerAdd", coq: "Z.add", lean: "_lean_addi", _: "add_int"} : (int, int) -> int

overload operator + = {add_atom, add_int}

// ***** Subtraction *****

val sub_atom = pure {ocaml: "sub_int", interpreter: "sub_int", lem: "integerMinus", coq: "Z.sub", lean: "_lean_subi", _: "sub_int"} : forall 'n 'm.
  (int('n), int('m)) -> int('n - 'm)

val sub_int = pure {ocaml: "sub_int", interpreter: "sub_int", lem: "integerMinus", coq: "Z.sub", lean: "_lean_subi", _: "sub_int"} : (int, int) -> int

overload operator - = {sub_atom, sub_int}

val sub_nat = pure {
  ocaml: "(fun (x,y) -> let n = sub_int (x,y) in if Big_int.less_equal n Big_int.zero then Big_int.zero else n)",
  lem: "integerMinus",
  coq: "Z.sub",
  lean: "_lean_subi",
  _: "sub_nat"
} : (nat, nat) -> nat

// ***** Negation *****

val negate_atom = pure {ocaml: "negate", interpreter: "negate", lem: "integerNegate", coq: "Z.opp", lean: "Neg.neg", _: "neg_int"} : forall 'n. int('n) -> int(- 'n)

val negate_int = pure {ocaml: "negate", interpreter: "negate", lem: "integerNegate", coq: "Z.opp", lean: "Neg.neg", _: "neg_int"} : int -> int

overload negate = {negate_atom, negate_int}

// ***** Multiplication *****

val mult_atom = pure {ocaml: "mult", interpreter: "mult", lem: "integerMult", coq: "Z.mul", lean: "_lean_muli", _: "mult_int"} : forall 'n 'm.
  (int('n), int('m)) -> int('n * 'm)

val mult_int = pure {ocaml: "mult", interpreter: "mult", lem: "integerMult", coq: "Z.mul", lean: "_lean_muli", _: "mult_int"} : (int, int) -> int

overload operator * = {mult_atom, mult_int}

$ifndef PRINT_EFFECTS

$[sv_module { stdout = true }]
val print_int = pure "print_int" : (string, int) -> unit

$[sv_module { stderr = true }]
val prerr_int = pure "prerr_int" : (string, int) -> unit

$else

val print_int = impure "print_int_effect" : (string, int) -> unit

val prerr_int = impure "prerr_int_effect" : (string, int) -> unit

$endif

$ifdef STRICT_EXPONENTIALS

val pow2 = pure {lean : "_lean_pow2i", _:"pow2"} : forall 'n, 'n >= 0. int('n) -> int(2 ^ 'n)

$else

/*!
We have special support for raising values to the power of two. Any Sail expression `2 ^ x` will be compiled to this builtin.
*/
val pow2 = pure {lean : "_lean_pow2i", _:"pow2"} : forall 'n. int('n) -> int(2 ^ 'n)

$endif

// ***** Integer shifts *****

/*!
A common idiom in asl is to take two bits of an opcode and convert in into a variable like
```
let elsize = shl_int(8, UInt(size))
```
THIS ensures that in this case the typechecker knows that the end result will be a value in the set `{8, 16, 32, 64}`

Similarly, we define shifts of 32 and 1 (i.e., powers of two).

The most general shift operations also allow negative shifts which go in the opposite direction, for compatibility with ASL.
*/
val _shl8 = pure {c: "shl_mach_int", lean: "Int.shiftl", _: "shl_int"} :
  forall 'n, 0 <= 'n <= 3. (int(8), int('n)) -> {'m, 'm in {8, 16, 32, 64}. int('m)}

val _shl32 = pure {c: "shl_mach_int", lean: "Int.shiftl", _: "shl_int"} :
  forall 'n, 'n in {0, 1}. (int(32), int('n)) -> {'m, 'm in {32, 64}. int('m)}

val _shl1 = pure {c: "shl_mach_int", lean: "Int.shiftl", _: "shl_int"} :
  forall 'n, 0 <= 'n <= 3. (int(1), int('n)) -> {'m, 'm in {1, 2, 4, 8}. int('m)}

val _shl_int = pure {
  lean: "Int.shiftl",
  _: "shl_int"
} : forall 'n, 0 <= 'n. (int, int('n)) -> int

val _shr32 = pure {
  c: "shr_mach_int",
  lean: "Int.shiftl",
  _: "shr_int"
} : forall 'n, 0 <= 'n <= 31. (int('n), int(1)) -> {'m, 0 <= 'm <= 15. int('m)}

val _shr_int = pure {
  lean: "Int.shiftr",
  _: "shr_int"
} : forall 'n, 0 <= 'n. (int, int('n)) -> int

function _shl_int_general(m: int, n: int) -> int = if n >= 0 then _shl_int(m, n) else _shr_int(m, negate(n))
function _shr_int_general(m: int, n: int) -> int = if n >= 0 then _shr_int(m, n) else _shl_int(m, negate(n))

overload shl_int = {_shl1, _shl8, _shl32, _shl_int, _shl_int_general}
overload shr_int = {_shr32, _shr_int, _shr_int_general}

// ***** div and mod *****

/*! Truncating division (rounds towards zero) */
val tdiv_int = pure {
  coq: "Z.quot",
  lean: "Int.tdiv",
  _: "tdiv_int"
} : (int, int) -> int

/*! Remainder for truncating division (has sign of dividend) */
val _tmod_int = pure {
  coq: "Z.rem",
  lean: "Int.tmod",
  _: "tmod_int"
} : (int, int) -> int

/*! If we know the second argument is positive, we know the result is positive */
val _tmod_int_positive = pure {
  ocaml: "tmod_int",
  interpreter: "tmod_int",
  lem: "tmod_int",
  coq: "Z.rem",
  lean: "Int.tmod",
  _: "tmod_int"
} : forall 'n, 'n >= 1. (int, int('n)) -> nat

overload tmod_int = {_tmod_int_positive, _tmod_int}

$c_reserved fdiv_int

function fdiv_int(n: int, m: int) -> int = {
  if n < 0 & m > 0 then {
    tdiv_int(n + 1, m) - 1
  } else if n > 0 & m < 0 then {
    tdiv_int(n - 1, m) - 1
  } else {
    tdiv_int(n, m)
  }
}

$c_reserved fmod_int

function fmod_int(n: int, m: int) -> int = {
  n - (m * fdiv_int(n, m))
}

val abs_int_plain = pure {
  smt : "abs",
  ocaml: "abs_int",
  interpreter: "abs_int",
  lem: "integerAbs",
  coq: "Z.abs",
  lean: "Sail.Int.intAbs",
  _: "abs_int"
} : int -> int

overload abs_int = {abs_int_plain}

val max_int = pure {
  lem: "integerMax",
  coq: "Z.max",
  lean: "Max.max",
  _: "max_int"
} : forall 'x 'y.
  (int('x), int('y)) -> {'z, ('x >= 'y & 'z == 'x) | ('x < 'y & 'z == 'y). int('z)}

val min_int = pure {
  lem: "integerMin",
  coq: "Z.min",
  lean: "Min.min",
  _: "min_int"
} : forall 'x 'y.
  (int('x), int('y)) -> {'z, ('x < 'y & 'z == 'x) | ('x >= 'y & 'z == 'y). int('z)}

$endif
