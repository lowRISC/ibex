/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_ADD
$define _FLOAT_ADD

$include <float/common.sail>
$include <float/nan.sail>
$include <float/arith_internal.sail>

val      float_add : forall 'n, 'n in {16, 32, 64, 128}. (bits('n), bits('n))
  -> (bits('n), fp_exception_flags)
function float_add (op_0, op_1) = {
  let same_sign = is_highest_zero (xor_vec (op_0, op_1));

  let (sum, flags) = if same_sign
                     then float_add_internal (op_0, op_1)
                     else float_sub_internal (op_0, op_1);
  (sum, flags);
}

$endif
