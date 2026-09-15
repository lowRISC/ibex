/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_ZERO
$define _FLOAT_ZERO

$include <float/common.sail>

val      float_is_zero : fp_bits -> bool
function float_is_zero (op) = {
  let struct {_, exp, mantissa} = float_decompose(op);
  let is_zero                   = is_all_zeros (exp) & is_all_zeros (mantissa);

  is_zero
}

$endif
