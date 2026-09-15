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

$ifndef _STRING
$define _STRING

$include <arith.sail>

val eq_string = pure {
   lem: "eq",
   coq: "generic_eq",
   lean: "_lean_beq",
   _: "eq_string"} : (string, string) -> bool

overload operator == = {eq_string}

val concat_str = pure {
   coq: "String.append",
   lem: "stringAppend",
   lean: "HAppend.hAppend",
   _: "concat_str"} : (string, string) -> string

val dec_str = pure {
  lean: "Int.repr",
  _: "dec_str"} : int -> string

val hex_str = pure { lean: "Int.toHex", _: "hex_str" } : int -> string

val hex_str_upper = pure { lean: "Int.toHexUpper", _: "hex_str_upper"} : int -> string

val bits_str = pure {
   lean: "BitVec.toFormatted",
   _: "string_of_bits"} : forall 'n. bitvector('n, dec) -> string

val concat_str_bits : forall 'n. (string, bitvector('n, dec)) -> string

function concat_str_bits(str, x) = concat_str(str, bits_str(x))

val concat_str_dec : (string, int) -> string

function concat_str_dec(str, x) = concat_str(str, dec_str(x))

/* Usually printing is used for diagnostic messages that are not part of the architecture and can
   be ignored during theorem proving.  It is often helpful to do this to reduce the amount of
   side-effects present in the model, but we also provide an alternative version that collects
   messages (currently supported by the Coq back-end). */

$ifndef PRINT_EFFECTS

$[sv_module { stdout = true }]
val print_endline = pure "print_endline" : string -> unit

$[sv_module { stderr = true }]
val prerr_endline = pure "prerr_endline" : string -> unit

$[sv_module { stdout = true }]
val print = pure "print" : string -> unit

$[sv_module { stderr = true }]
val prerr = pure "prerr" : string -> unit

$else

val print_endline = impure "print_endline_effect" : string -> unit

val prerr_endline = impure "prerr_endline_effect" : string -> unit

val print = impure "print_effect" : string -> unit

val prerr = impure "prerr_effect" : string -> unit

$endif

$endif
