/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* accessors for default architectural addresses, for use from within instructions */

/*!
  Retrieves the architectural PC value. This is not necessarily the value
  found in the PC register as extensions may choose to override this function.
  The value in the PC register is the absolute virtual address of the instruction
  to fetch.
 */
val get_arch_pc : unit -> xlenbits
function get_arch_pc() = PC

val get_next_pc : unit -> xlenbits
function get_next_pc() = nextPC

val set_next_pc : xlenbits -> unit
function set_next_pc(pc) = {
  nextPC = pc
}

val tick_pc : unit -> unit
function tick_pc() = {
  PC = nextPC
}
