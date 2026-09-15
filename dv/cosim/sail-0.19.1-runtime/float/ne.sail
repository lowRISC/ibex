/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_NE
$define _FLOAT_NE

$include <float/common.sail>
$include <float/nan.sail>
$include <float/arith_internal.sail>

val      float_is_ne : fp_bits_x2 -> fp_bool_and_flags
function float_is_ne ((op_0, op_1)) = {
  let is_snan = float_is_snan (op_0) | float_is_snan (op_1);
  let flags   = if   is_snan
                then fp_eflag_invalid
                else fp_eflag_none;

  let is_nan  = float_is_nan (op_0) | float_is_nan (op_1);
  let is_ne   = not (is_nan) & float_is_ne_internal ((op_0, op_1));

  (is_ne, flags);
}

$endif
