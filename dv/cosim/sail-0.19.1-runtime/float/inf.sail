/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_INF
$define _FLOAT_INF

$include <float/common.sail>

val      float_is_inf : fp_bits -> bool
function float_is_inf (op) = {
  let struct {_, exp, mantissa} = float_decompose(op);
  let is_inf                    = is_all_ones (exp) & is_all_zeros (mantissa);

  is_inf
}

$endif
