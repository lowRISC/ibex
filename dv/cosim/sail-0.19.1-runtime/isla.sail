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

$ifndef _ISLA
$define _ISLA

$ifdef SYMBOLIC

val isla_reset_registers = pure "reset_registers" : unit -> unit

val isla_log_event = pure "log_event" : forall ('a: Type). (string, 'a) -> unit

val isla_synchronize_registers = pure "synchronize_registers" : unit -> unit

val isla_mark_register = pure "mark_register" : forall ('a: Type). (register('a), string) -> unit

val isla_mark_register_pair = pure "mark_register_pair" : forall ('a: Type) ('b: Type). (register('a), register('b), string) -> unit

val isla_monomorphize = pure "monomorphize" : forall 'n, 'n >= 0. bits('n) -> bits('n)

val isla_interrupt_pending = pure "interrupt_pending" : unit -> bool

$else

val isla_reset_registers : unit -> unit

function isla_reset_registers() = ()

val isla_log_event : forall ('a: Type). (string, 'a) -> unit

function isla_log_event(_, _) = ()

val isla_synchronize_registers : unit -> unit

function isla_synchronize_registers() = ()

val isla_mark_register : forall ('a: Type). (register('a), string) -> unit

function isla_mark_register(_, _) = ()

val isla_mark_register_pair : forall ('a: Type) ('b: Type). (register('a), register('b), string) -> unit

function isla_mark_register_pair(_, _, _) = ()

val isla_monomorphize : forall 'n, 'n >= 0. bits('n) -> bits('n)

function isla_monomorphize bv = bv

val isla_interrupt_pending : unit -> bool

function isla_interrupt_pending() = false

$endif

val isla_ignore_write_to : forall ('a: Type). register('a) -> unit

function isla_ignore_write_to(reg) = isla_mark_register(reg, "ignore_write")

$endif
