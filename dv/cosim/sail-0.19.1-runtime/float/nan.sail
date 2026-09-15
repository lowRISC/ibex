/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_NAN
$define _FLOAT_NAN

$include <float/common.sail>

val      float_is_nan : fp_bits -> bool
function float_is_nan (op) = {
  let struct {_, exp, mantissa} = float_decompose(op);
  let is_nan                    = is_all_ones (exp) & not (is_all_zeros (mantissa));

  is_nan
}

val      float_is_snan : fp_bits -> bool
function float_is_snan (op) = {
  let struct {_, mantissa} = float_decompose(op);
  let is_snan              = float_is_nan (op) & is_highest_zero (mantissa);

  is_snan
}

val      float_is_qnan : fp_bits -> bool
function float_is_qnan (op) = {
  let struct {_, mantissa} = float_decompose(op);
  let is_qnan              = float_is_nan (op) & is_highest_one (mantissa);

  is_qnan
}

$endif
