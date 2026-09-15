/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* The default metadata carries no information, and is implemented
 * using a unit type.
 */

type mem_meta = unit

let default_meta : mem_meta = ()

val __WriteRAM_Meta : forall 'n. (xlenbits, atom('n), mem_meta) -> unit
function __WriteRAM_Meta(addr, width, meta) = ()

val __ReadRAM_Meta  : forall 'n. (xlenbits, atom('n)) -> mem_meta
function __ReadRAM_Meta(addr, width) = ()
