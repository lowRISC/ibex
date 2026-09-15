/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_COMMON
$define _FLOAT_COMMON

/* Floating point types definition */
type fp_exception_flags = bits(5) /* Floating-point exception flags. */
type fp_rounding_modes = bits(5) /* Floating-point rounding modes. */
type fp_bits = { 'n, 'n in {16, 32, 64, 128}. bits('n) } /* Floating-point in bits. */
type fp_bits_x2 = { 'n, 'n in {16, 32, 64, 128}. (bits('n), bits('n)) } /* Floating point x2 tuple */
type fp_bool_and_flags = (bool, fp_exception_flags) /* Floating point bool and exception flags tuple */

/* Floating point constants */
let fp_eflag_none           : fp_exception_flags = 0b00000
let fp_eflag_invalid        : fp_exception_flags = 0b00001
let fp_eflag_divide_by_zero : fp_exception_flags = 0b00010
let fp_eflag_oveflow        : fp_exception_flags = 0b00100
let fp_eflag_underflow      : fp_exception_flags = 0b01000
let fp_eflag_inexact        : fp_exception_flags = 0b10000

let fp_eflag_overflow_and_inexact : fp_exception_flags = fp_eflag_oveflow | fp_eflag_inexact

let fp_rounding_rne     : fp_rounding_modes = 0b00001
let fp_rounding_rna     : fp_rounding_modes = 0b00010
let fp_rounding_rdn     : fp_rounding_modes = 0b00011
let fp_rounding_rup     : fp_rounding_modes = 0b00100
let fp_rounding_rtz     : fp_rounding_modes = 0b00101
let fp_rounding_default : fp_rounding_modes = fp_rounding_rne

/* Floating point global variables */
register fp_rounding_global : fp_rounding_modes = fp_rounding_default

/* Floating point struct */
struct float_bits('n : Int) = {
  sign     : bits(1),
  exp      : bits(if  'n == 16
                  then 5
                  else (if   'n == 32
                        then 8
                        else (if   'n == 64
                              then 11
                              else 15))),
  mantissa : bits(if  'n == 16
                  then 10
                  else (if   'n == 32
                        then 23
                        else (if   'n == 64
                              then 52
                              else 112))),
}

/* The val func implementations */
val      float_decompose : forall 'n, 'n in { 16, 32, 64, 128 }. bits('n) -> float_bits('n)
function float_decompose(op) = {
  match 'n {
    16 => struct {
      sign     = op[15..15],
      exp      = op[14..10],
      mantissa = op[9..0],
    },
    32 => struct {
      sign     = op[31..31],
      exp      = op[30..23],
      mantissa = op[22..0],
    },
    64 => struct {
      sign      = op[63..63],
      exp       = op[62..52],
      mantissa  = op[51..0],
    },
    128 => struct {
      sign      = op[127..127],
      exp       = op[126..112],
      mantissa  = op[111..0],
    }
  }
}

val      float_compose : forall 'n, 'n in { 16, 32, 64, 128 }. float_bits('n) -> bits('n)
function float_compose(op) = op.sign @ op.exp @ op.mantissa

val      float_has_max_exp : forall 'n, 'n in { 16, 32, 64, 128 }. bits('n) -> bool
function float_has_max_exp (op) = {
  let fp = float_decompose (op);
  let bitsize = length (op);
  let one = sail_zero_extend ([bitone], bitsize);
  let two = sail_shiftleft (one, 1);
  let max_exp = sub_bits (sail_shiftleft (one, length (fp.exp)), two);
  let has_max = max_exp == sail_zero_extend (fp.exp, bitsize);

  has_max;
}

val      not : forall ('p : Bool). bool('p) -> bool(not('p))
function not(b) = not_bool(b)

val      is_lowest_one : forall 'n, 0 < 'n. bits('n) -> bool
function is_lowest_one (op) = op[0] == bitone

val      is_highest_one : forall 'n, 0 < 'n. bits('n) -> bool
function is_highest_one (op) = op['n - 1] == bitone

val      is_all_ones : forall 'n, 0 < 'n. bits('n) -> bool
function is_all_ones (op) = op == sail_ones ('n)

val      is_lowest_zero : forall 'n, 0 < 'n. bits('n) -> bool
function is_lowest_zero (op) = op[0] == bitzero

val      is_highest_zero : forall 'n, 0 < 'n. bits('n) -> bool
function is_highest_zero (op) = op['n - 1] == bitzero

val      is_all_zeros : forall 'n, 0 < 'n. bits('n) -> bool
function is_all_zeros (op) = op == sail_zeros ('n)

$endif
