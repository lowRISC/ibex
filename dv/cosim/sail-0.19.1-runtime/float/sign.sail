/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_SIGN
$define _FLOAT_SIGN

$include <float/common.sail>

val      float_is_positive : fp_bits -> bool
function float_is_positive (op) = {
  let is_positive = is_highest_zero (op);

  is_positive
}

val      float_is_negative : fp_bits -> bool
function float_is_negative (op) = {
  let is_negative = is_highest_one (op);

  is_negative
}

$endif
