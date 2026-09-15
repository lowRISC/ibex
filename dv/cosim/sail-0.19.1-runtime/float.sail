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

$sail_internal

$ifndef _FLOATING_POINT
$define _FLOATING_POINT

// rounding_mode name already in use by various specifications
type rounding_mode = float_rounding_mode

val round_nearest_ties_to_even = pure "round_nearest_ties_to_even" : unit -> rounding_mode
val round_nearest_ties_to_away = pure "round_nearest_ties_to_away" : unit -> rounding_mode
val round_toward_positive = pure "round_toward_positive" : unit -> rounding_mode
val round_toward_negative = pure "round_toward_negative" : unit -> rounding_mode
val round_toward_zero = pure "round_toward_zero" : unit -> rounding_mode

val undefined_float16 = impure "fp16_undefined" : unit -> float16
val undefined_float32 = impure "fp32_undefined" : unit -> float32
val undefined_float64 = impure "fp64_undefined" : unit -> float64
val undefined_float128 = impure "fp128_undefined" : unit -> float128

val fp16_nan = pure "fp16_nan" : unit -> float16
val fp32_nan = pure "fp32_nan" : unit -> float32
val fp64_nan = pure "fp64_nan" : unit -> float64
val fp128_nan = pure "fp128_nan" : unit -> float128

val fp16_inf = pure "fp16_inf" : unit -> float16
val fp32_inf = pure "fp32_inf" : unit -> float32
val fp64_inf = pure "fp64_inf" : unit -> float64
val fp128_inf = pure "fp128_inf" : unit -> float128

val fp16_negative_inf = pure "fp16_negative_inf" : unit -> float16
val fp32_negative_inf = pure "fp32_negative_inf" : unit -> float32
val fp64_negative_inf = pure "fp64_negative_inf" : unit -> float64
val fp128_negative_inf = pure "fp128_negative_inf" : unit -> float128

val fp16_zero = pure "fp16_zero" : unit -> float16
val fp32_zero = pure "fp32_zero" : unit -> float32
val fp64_zero = pure "fp64_zero" : unit -> float64
val fp128_zero = pure "fp128_zero" : unit -> float128

val fp16_negative_zero = pure "fp16_negative_zero" : unit -> float16
val fp32_negative_zero = pure "fp32_negative_zero" : unit -> float32
val fp64_negative_zero = pure "fp64_negative_zero" : unit -> float64
val fp128_negative_zero = pure "fp128_negative_zero" : unit -> float128

val fp16_abs = pure "fp_abs" : float16 -> float16
val fp32_abs = pure "fp_abs" : float32 -> float32
val fp64_abs = pure "fp_abs" : float64 -> float64
val fp128_abs = pure "fp_abs" : float128 -> float128

val fp16_neg = pure "fp_neg" : float16 -> float16
val fp32_neg = pure "fp_neg" : float32 -> float32
val fp64_neg = pure "fp_neg" : float64 -> float64
val fp128_neg = pure "fp_neg" : float128 -> float128

val fp16_is_normal = pure "fp_is_normal" : float16 -> bool
val fp32_is_normal = pure "fp_is_normal" : float32 -> bool
val fp64_is_normal = pure "fp_is_normal" : float64 -> bool
val fp128_is_normal = pure "fp_is_normal" : float128 -> bool

val fp16_is_subnormal = pure "fp_is_subnormal" : float16 -> bool
val fp32_is_subnormal = pure "fp_is_subnormal" : float32 -> bool
val fp64_is_subnormal = pure "fp_is_subnormal" : float64 -> bool
val fp128_is_subnormal = pure "fp_is_subnormal" : float128 -> bool

val fp16_is_zero = pure "fp_is_zero" : float16 -> bool
val fp32_is_zero = pure "fp_is_zero" : float32 -> bool
val fp64_is_zero = pure "fp_is_zero" : float64 -> bool
val fp128_is_zero = pure "fp_is_zero" : float128 -> bool

val fp16_is_infinite = pure "fp_is_infinite" : float16 -> bool
val fp32_is_infinite = pure "fp_is_infinite" : float32 -> bool
val fp64_is_infinite = pure "fp_is_infinite" : float64 -> bool
val fp128_is_infinite = pure "fp_is_infinite" : float128 -> bool

val fp16_is_nan = pure "fp_is_nan" : float16 -> bool
val fp32_is_nan = pure "fp_is_nan" : float32 -> bool
val fp64_is_nan = pure "fp_is_nan" : float64 -> bool
val fp128_is_nan = pure "fp_is_nan" : float128 -> bool

val fp16_is_negative = pure "fp_is_negative" : float16 -> bool
val fp32_is_negative = pure "fp_is_negative" : float32 -> bool
val fp64_is_negative = pure "fp_is_negative" : float64 -> bool
val fp128_is_negative = pure "fp_is_negative" : float128 -> bool

val fp16_is_positive = pure "fp_is_positive" : float16 -> bool
val fp32_is_positive = pure "fp_is_positive" : float32 -> bool
val fp64_is_positive = pure "fp_is_positive" : float64 -> bool
val fp128_is_positive = pure "fp_is_positive" : float128 -> bool

$ifdef _DEFAULT_DEC

val fp16_from_ieee = pure "fp16_from_ieee" : bitvector(16, dec) -> float16
val fp32_from_ieee = pure "fp32_from_ieee" : bitvector(32, dec) -> float32
val fp64_from_ieee = pure "fp64_from_ieee" : bitvector(64, dec) -> float64
val fp128_from_ieee = pure "fp128_from_ieee" : bitvector(128, dec) -> float128

$endif

val fp16_sqrt = pure "fp_sqrt" : (rounding_mode, float16) -> float16
val fp32_sqrt = pure "fp_sqrt" : (rounding_mode, float32) -> float32
val fp64_sqrt = pure "fp_sqrt" : (rounding_mode, float64) -> float64
val fp128_sqrt = pure "fp_sqrt" : (rounding_mode, float128) -> float128

val fp16_round_to_integral = pure "fp_round_to_integral" : (rounding_mode, float16) -> float16
val fp32_round_to_integral = pure "fp_round_to_integral" : (rounding_mode, float32) -> float32
val fp64_round_to_integral = pure "fp_round_to_integral" : (rounding_mode, float64) -> float64
val fp128_round_to_integral = pure "fp_round_to_integral" : (rounding_mode, float128) -> float128

val fp16_to_fp32 = pure "fp32_convert" : (rounding_mode, float16) -> float32
val fp16_to_fp64 = pure "fp64_convert" : (rounding_mode, float16) -> float64
val fp16_to_fp128 = pure "fp128_convert" : (rounding_mode, float16) -> float128

val fp32_to_fp16 = pure "fp16_convert" : (rounding_mode, float32) -> float16
val fp32_to_fp64 = pure "fp64_convert" : (rounding_mode, float32) -> float64
val fp32_to_fp128 = pure "fp128_convert" : (rounding_mode, float32) -> float128

val fp64_to_fp16 = pure "fp16_convert" : (rounding_mode, float64) -> float16
val fp64_to_fp32 = pure "fp32_convert" : (rounding_mode, float64) -> float32
val fp64_to_fp128 = pure "fp128_convert" : (rounding_mode, float64) -> float128

val fp128_to_fp16 = pure "fp16_convert" : (rounding_mode, float128) -> float16
val fp128_to_fp32 = pure "fp32_convert" : (rounding_mode, float128) -> float32
val fp128_to_fp64 = pure "fp64_convert" : (rounding_mode, float128) -> float64

$ifdef _DEFAULT_DEC

val fp16_from_signed = pure "fp16_from_signed" : forall 'n, 'n > 0. (rounding_mode, bitvector('n, dec)) -> float16
val fp32_from_signed = pure "fp32_from_signed" : forall 'n, 'n > 0. (rounding_mode, bitvector('n, dec)) -> float32
val fp64_from_signed = pure "fp64_from_signed" : forall 'n, 'n > 0. (rounding_mode, bitvector('n, dec)) -> float64
val fp128_from_signed = pure "fp128_from_signed" : forall 'n, 'n > 0. (rounding_mode, bitvector('n, dec)) -> float128

val fp16_from_unsigned = pure "fp16_from_unsigned" : forall 'n, 'n > 0. (rounding_mode, bitvector('n, dec)) -> float16
val fp32_from_unsigned = pure "fp32_from_unsigned" : forall 'n, 'n > 0. (rounding_mode, bitvector('n, dec)) -> float32
val fp64_from_unsigned = pure "fp64_from_unsigned" : forall 'n, 'n > 0. (rounding_mode, bitvector('n, dec)) -> float64
val fp128_from_unsigned = pure "fp128_from_unsigned" : forall 'n, 'n > 0. (rounding_mode, bitvector('n, dec)) -> float128

$endif

val fp16_rem = pure "fp_rem" : (float16, float16) -> float16
val fp32_rem = pure "fp_rem" : (float32, float32) -> float32
val fp64_rem = pure "fp_rem" : (float64, float64) -> float64
val fp128_rem = pure "fp_rem" : (float128, float128) -> float128

val fp16_min = pure "fp_min" : (float16, float16) -> float16
val fp32_min = pure "fp_min" : (float32, float32) -> float32
val fp64_min = pure "fp_min" : (float64, float64) -> float64
val fp128_min = pure "fp_min" : (float128, float128) -> float128

val fp16_max = pure "fp_max" : (float16, float16) -> float16
val fp32_max = pure "fp_max" : (float32, float32) -> float32
val fp64_max = pure "fp_max" : (float64, float64) -> float64
val fp128_max = pure "fp_max" : (float128, float128) -> float128

val fp16_lteq = pure "fp_lteq" : (float16, float16) -> bool
val fp32_lteq = pure "fp_lteq" : (float32, float32) -> bool
val fp64_lteq = pure "fp_lteq" : (float64, float64) -> bool
val fp128_lteq = pure "fp_lteq" : (float128, float128) -> bool

val fp16_lt = pure "fp_lt" : (float16, float16) -> bool
val fp32_lt = pure "fp_lt" : (float32, float32) -> bool
val fp64_lt = pure "fp_lt" : (float64, float64) -> bool
val fp128_lt = pure "fp_lt" : (float128, float128) -> bool

val fp16_gteq = pure "fp_gteq" : (float16, float16) -> bool
val fp32_gteq = pure "fp_gteq" : (float32, float32) -> bool
val fp64_gteq = pure "fp_gteq" : (float64, float64) -> bool
val fp128_gteq = pure "fp_gteq" : (float128, float128) -> bool

val fp16_gt = pure "fp_gt" : (float16, float16) -> bool
val fp32_gt = pure "fp_gt" : (float32, float32) -> bool
val fp64_gt = pure "fp_gt" : (float64, float64) -> bool
val fp128_gt = pure "fp_gt" : (float128, float128) -> bool

val fp16_eq = pure "fp_eq" : (float16, float16) -> bool
val fp32_eq = pure "fp_eq" : (float32, float32) -> bool
val fp64_eq = pure "fp_eq" : (float64, float64) -> bool
val fp128_eq = pure "fp_eq" : (float128, float128) -> bool

val fp16_add = pure "fp_add" : (rounding_mode, float16, float16) -> float16
val fp32_add = pure "fp_add" : (rounding_mode, float32, float32) -> float32
val fp64_add = pure "fp_add" : (rounding_mode, float64, float64) -> float64
val fp128_add = pure "fp_add" : (rounding_mode, float128, float128) -> float128

val fp16_sub = pure "fp_sub" : (rounding_mode, float16, float16) -> float16
val fp32_sub = pure "fp_sub" : (rounding_mode, float32, float32) -> float32
val fp64_sub = pure "fp_sub" : (rounding_mode, float64, float64) -> float64
val fp128_sub = pure "fp_sub" : (rounding_mode, float128, float128) -> float128

val fp16_mul = pure "fp_mul" : (rounding_mode, float16, float16) -> float16
val fp32_mul = pure "fp_mul" : (rounding_mode, float32, float32) -> float32
val fp64_mul = pure "fp_mul" : (rounding_mode, float64, float64) -> float64
val fp128_mul = pure "fp_mul" : (rounding_mode, float128, float128) -> float128

val fp16_div = pure "fp_div" : (rounding_mode, float16, float16) -> float16
val fp32_div = pure "fp_div" : (rounding_mode, float32, float32) -> float32
val fp64_div = pure "fp_div" : (rounding_mode, float64, float64) -> float64
val fp128_div = pure "fp_div" : (rounding_mode, float128, float128) -> float128

val fp16_fma = pure "fp_fma" : (rounding_mode, float16, float16, float16) -> float16
val fp32_fma = pure "fp_fma" : (rounding_mode, float32, float32, float32) -> float32
val fp64_fma = pure "fp_fma" : (rounding_mode, float64, float64, float64) -> float64
val fp128_fma = pure "fp_fma" : (rounding_mode, float128, float128, float128) -> float128

$endif _FLOATING_POINT
