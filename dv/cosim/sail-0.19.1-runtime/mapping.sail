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

$ifndef _MAPPING
$define _MAPPING

$include <arith.sail>
$include <option.sail>

$[sv_function { types = "int #1" }]
val string_take = pure {
  lean: "String.take",
  _: "string_take"
}: (string, nat) -> string

$[sv_function { types = "int #1" }]
val string_drop = pure {
  lean: "String.drop",
  _: "string_drop"
}: (string, nat) -> string

$[sv_function { return_type = "int" }]
val string_length = pure {
  lean: "String.length",
  _: "string_length"
}: string -> nat

val string_append = pure {
  coq: "String.append",
  lean: "String.append",
  c: "concat_str",
  _: "string_append"
} : (string, string) -> string

val string_startswith = pure {
  lean: "String.startsWith",
  _: "string_startswith"
}: (string, string) -> bool

val n_leading_spaces = pure { coq: "n_leading_spaces_Z", lean: "String.leadingSpaces" } : string -> nat
function n_leading_spaces s =
  match s {
    "" => 0,
    _ => match string_take(s, 1) {
      " " => 1 + n_leading_spaces(string_drop(s, 1)),
      _ => 0
    }
  }

/*!
In a string mapping this is treated as `[ ]+`, i.e one or more space
characters. It is printed as a single space `" "`.
*/
val spc : unit <-> string

function spc_forwards() = " "
function spc_forwards_matches() = true

function spc_backwards _ = ()
function spc_backwards_matches s = {
  let len = string_length(s);
  n_leading_spaces(s) == len & len > 0
}

/*!
In a string mapping this is treated as `[ ]*`, i.e. zero or more space
characters. It is printed as the empty string.
*/
val opt_spc : unit <-> string

function opt_spc_forwards() = ""
function opt_spc_forwards_matches() = true

function opt_spc_backwards _ = ()
function opt_spc_backwards_matches s = n_leading_spaces(s) == string_length(s)

/*!
Like `opt_spc`, in a string mapping this is treated as `[ ]*`, i.e. zero or more space
characters. It differs however in that it is printed as a single space `" "`.
*/
val def_spc : unit <-> string

function def_spc_forwards() = " "
function def_spc_forwards_matches() = true

function def_spc_backwards _ = ()
function def_spc_backwards_matches s = n_leading_spaces(s) == string_length(s)

mapping sep : unit <-> string = {
  () <-> opt_spc() ^ "," ^ def_spc()
}

$endif
