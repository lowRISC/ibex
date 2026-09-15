/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_LT
$define _FLOAT_LT

$include <float/common.sail>
$include <float/nan.sail>
$include <float/arith_internal.sail>

val      float_is_lt : fp_bits_x2 -> fp_bool_and_flags
function float_is_lt ((op_0, op_1)) = {
  let is_nan  = float_is_nan (op_0) | float_is_nan (op_1);
  let flags   = if   is_nan
                then fp_eflag_invalid
                else fp_eflag_none;
  let is_lt   = not (is_nan) & float_is_lt_internal ((op_0, op_1));

  (is_lt, flags);
}

$endif
