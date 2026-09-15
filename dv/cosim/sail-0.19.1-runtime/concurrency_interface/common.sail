/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$sail_internal

$target_set emulator_or_isla isla c ocaml interpreter systemverilog
$target_set emulator c ocaml interpreter systemverilog
$target_set prover lem coq lean

$ifndef _CONCURRENCY_INTERFACE_COMMON
$define _CONCURRENCY_INTERFACE_COMMON

$ifdef _DEFAULT_DEC
$include <vector_dec.sail>
$else
$include <vector_inc.sail>
$endif

$include <option.sail>
$include <result.sail>

$include <concurrency_interface/emulator_memory.sail>

$ifdef SYMBOLIC
val sail_instr_announce
  = impure "instr_announce"
  : forall 'n, 'n > 0.
  bits('n) -> unit
$else
/*! Each cycle (see [sail_end_cycle]) the model must announce the
  current opcode being executed. This is so each event within a cycle
  can be associated with an instruction. */
val sail_instr_announce : forall 'n, 'n > 0. bits('n) -> unit

function sail_instr_announce _ = ()
$endif

$ifdef SYMBOLIC
val sail_branch_announce
  = impure "branch_announce"
  : forall 'addrsize, 'addrsize in {32, 64}.
  (int('addrsize), bits('addrsize)) -> unit
$else
/*! For keeping track of control dependencies, when we take a branch
  we announce the address we are branching to. */
val sail_branch_announce : forall 'addrsize, 'addrsize in {32, 64}.
  (int('addrsize), bits('addrsize)) -> unit

function sail_branch_announce(_, _) = ()
$endif

/*! Each fetch-decode-execute cycle, the Sail model is expected to
  call [sail_end_cycle], to increment the cycle count and indicate the
  end of the current instruction. Cycle 0 is reserved for
  initialisation before executing the first instruction. */
val sail_end_cycle = impure "cycle_count" : unit -> unit

/*! Returns the current cycle count */
$[sv_function { return_type = int }]
val sail_get_cycle_count = impure "get_cycle_count" : unit -> int

$ifdef SYMBOLIC
val sail_reset_registers = pure "reset_registers" : unit -> unit

val sail_synchronize_registers = pure "synchronize_registers" : unit -> unit
$else
/*! Isla allows registers to be set on the command line via the
  `-R/--register` flag. This function sets those registers to the
  provided values. It is a no-op for non-Isla targets.

  This enables a startup flow that works something like:
  ```sail
  function main() {
    // registers can be set using -I/--initial here
    initialize_model(); // defined by the architecture
    sail_reset_registers(); // registers can be set using -R/--register here
    ...
  ```

  This allows us to set the values of registers that would otherwise
  be initialised to some sensible default by the `initialize_model`
  function (overwriting a value set by `-I` at the beginning of execution). */
val sail_reset_registers : unit -> unit

function sail_reset_registers() = ()

/*! Isla supports *relaxed* semantics for system registers. This works
  as follows: Writes to these registers are not guaranteed to occur
  immediately. When a value is read from such a register, any previous
  written value can be read. Re-reading the register within the same
  instruction is guaranteed to return the same value ([sail_end_cycle]
  allows a different value to be subsequently read).

  This function removes all but the very last write, so subsequent
  reads must see only that value.

  This function is a no-op for non-Isla targets. */
val sail_synchronize_registers : unit -> unit

function sail_synchronize_registers() = ()
$endif

$ifdef SYMBOLIC
val sail_mark_register = pure "mark_register" : forall ('a: Type). (register('a), string) -> unit

val sail_mark_register_pair = pure "mark_register_pair" : forall ('a: Type) ('b: Type). (register('a), register('b), string) -> unit
$else
/*! The functions [sail_mark_register] and [sail_mark_register_pair]
  allow some information in the form of a string to be attached to some
  registers in an execution trace.

  These functions are a no-op for non-Isla targets. */
val sail_mark_register : forall ('a: Type). (register('a), string) -> unit

function sail_mark_register(_, _) = ()

val sail_mark_register_pair : forall ('a: Type) ('b: Type). (register('a), register('b), string) -> unit

function sail_mark_register_pair(_, _, _) = ()
$endif

/*! The function THIS will cause dependency analysis in Isla to ignore
  the write to the given register. */
val sail_ignore_write_to : forall ('a: Type). register('a) -> unit

function sail_ignore_write_to(reg) = sail_mark_register(reg, "ignore_write")

val sail_pick_dependency : forall ('a: Type). register('a) -> unit

function sail_pick_dependency(reg) = sail_mark_register(reg, "pick")

$ifdef SYMBOLIC
val __monomorphize = pure "monomorphize" : forall 'n, 'n >= 0. bits('n) -> bits('n)
$else
val __monomorphize : forall 'n, 'n >= 0. bits('n) -> bits('n)

function __monomorphize(bv) = bv
$endif

$endif
