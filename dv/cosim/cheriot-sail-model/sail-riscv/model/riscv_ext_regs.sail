/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* This file contains register handling functions that can be
 * overridden by extensions.
 */

val ext_init_regs : unit -> unit
function ext_init_regs () = ()

/*!
This function is called after above when running rvfi and allows the model
to be initialised differently (e.g. CHERI cap regs are initialised
to omnipotent instead of null).
 */
val ext_rvfi_init : unit -> unit
function ext_rvfi_init () = {
  x1 = x1 // to avoid hook being optimized out
}


/*!
THIS(csrno, priv, isWrite) allows an extension to block access to csrno,
at Privilege level priv. It should return true if the access is allowed.
*/
val ext_check_CSR : (bits(12), Privilege, bool) -> bool
function ext_check_CSR (csrno, p, isWrite) = true

/*!
THIS is called if ext_check_CSR returns false. It should
cause an appropriate RISCV exception.
 */
val ext_check_CSR_fail : unit->unit
function ext_check_CSR_fail () = ()
