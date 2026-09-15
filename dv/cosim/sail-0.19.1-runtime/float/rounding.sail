/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_ROUNDING
$define _FLOAT_ROUNDING

$include <float/common.sail>

val      float_get_rounding : unit -> fp_rounding_modes
function float_get_rounding () = {
  fp_rounding_global;
}

val      float_set_rounding : fp_rounding_modes -> unit
function float_set_rounding (rm) = {
  fp_rounding_global = rm;
}

$endif
