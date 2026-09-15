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

$ifndef _SMT
$define _SMT

// see http://smtlib.cs.uiowa.edu/theories-Ints.shtml

/*! Euclidean division */
val ediv_int = pure {
  ocaml: "quotient",
  interpreter: "quotient",
  lem: "integerDiv",
  coq: "ZEuclid.div",
  lean: "Int.ediv",
  _: "ediv_int"
} : forall 'n 'm. (int('n), int('m)) -> int(div('n, 'm))

val emod_int = pure {
  ocaml: "modulus",
  interpreter: "modulus",
  lem: "integerMod",
  coq: "ZEuclid.modulo",
  lean: "Int.emod",
  _: "emod_int"
} : forall 'n 'm. (int('n), int('m)) -> int(mod('n, 'm))

val abs_int_atom = pure {
  ocaml: "abs_int",
  interpreter: "abs_int",
  lem: "integerAbs",
  coq: "Z.abs",
  lean: "Int.natAbs",
  _: "abs_int"
} : forall 'n. int('n) -> int(abs('n))

overload abs_int = {abs_int_atom}

$ifdef TEST

let __smt_x : int(div(4, 2)) = div(8, 4)

$endif

$endif
