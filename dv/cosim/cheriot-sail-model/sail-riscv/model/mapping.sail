// Note: This file is temporarily copied here from the Sail compiler. It can
// be removed when Sail 0.18 is released.

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
/*  Redistribution and use in source and binary forms, with or without      */
/*  modification, are permitted provided that the following conditions      */
/*  are met:                                                                */
/*  1. Redistributions of source code must retain the above copyright       */
/*     notice, this list of conditions and the following disclaimer.        */
/*  2. Redistributions in binary form must reproduce the above copyright    */
/*     notice, this list of conditions and the following disclaimer in      */
/*     the documentation and/or other materials provided with the           */
/*     distribution.                                                        */
/*                                                                          */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      */
/*  SUCH DAMAGE.                                                            */
/*==========================================================================*/

$ifndef _MAPPING
$define _MAPPING

$include <arith.sail>
$include <option.sail>

val string_take = pure "string_take" : (string, nat) -> string
val string_drop = pure "string_drop" : (string, nat) -> string
val string_length = pure "string_length" : string -> nat
val string_append = pure {coq: "String.append", c: "concat_str", _: "string_append"} : (string, string) -> string
val string_startswith = pure "string_startswith" : (string, string) -> bool

val n_leading_spaces = pure { coq: "n_leading_spaces_Z" } : string -> nat
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
