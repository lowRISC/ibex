/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Extensions may wish to interpose and transform decoded instructions,
 * based on other machine state. This is supported via decode instruction
  hooks, the default implementation of which is provided below.
 */

val ext_decode_compressed : bits(16) -> ast
function ext_decode_compressed(bv) = encdec_compressed(bv)

val ext_decode : bits(32) -> ast
function ext_decode(bv) = encdec(bv)
