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

$ifndef _REAL
$define _REAL

val "neg_real" : real -> real

val "mult_real" : (real, real) -> real

overload operator * = {mult_real}

val "sub_real" : (real, real) -> real

overload operator - = {sub_real}

val "add_real" : (real, real) -> real

overload operator + = {add_real}

val "div_real" : (real, real) -> real

overload operator / = {div_real}

val sqrt = pure "sqrt_real" : real -> real

val "abs_real" : real -> real

val floor = pure "round_down" : real -> int

val ceil = pure "round_up" : real -> int

val "to_real" : int -> real

val "eq_real" : (real, real) -> bool
val "lt_real" : (real, real) -> bool
val "gt_real" : (real, real) -> bool
val "lteq_real" : (real, real) -> bool
val "gteq_real" : (real, real) -> bool

overload operator == = {eq_real}
overload operator < = {lt_real}
overload operator > = {gt_real}
overload operator <= = {lteq_real}
overload operator >= = {gteq_real}

val pow_real = pure "real_power" : (real, int) -> real

val "print_real" : (string, real) -> unit
val "prerr_real" : (string, real) -> unit

val "random_real" : unit -> real

$endif
