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

$ifndef _DEC_BITS
$define _DEC_BITS

$include <option.sail>
$include <vector.sail>
$include <string.sail>

val "parse_dec_bits" : forall 'n, 'n > 0. (int('n), string) -> bits('n)

val "valid_dec_bits" : forall 'n, 'n > 0. (int('n), string) -> bool

val dec_bits : forall 'n, 'n > 0. bits('n) <-> (int('n), string)

function dec_bits_forwards(bv) = (length(bv), dec_str(unsigned(bv)))
function dec_bits_forwards_matches(bv) = true

function dec_bits_backwards(n, str) = parse_dec_bits(n, str)
function dec_bits_backwards_matches(n, str) = valid_dec_bits(n, str)

mapping dec_bits_1 : bits(1) <-> string = { dec_bits(1, s) <-> s }
mapping dec_bits_2 : bits(2) <-> string = { dec_bits(2, s) <-> s }
mapping dec_bits_3 : bits(3) <-> string = { dec_bits(3, s) <-> s }
mapping dec_bits_4 : bits(4) <-> string = { dec_bits(4, s) <-> s }
mapping dec_bits_5 : bits(5) <-> string = { dec_bits(5, s) <-> s }
mapping dec_bits_6 : bits(6) <-> string = { dec_bits(6, s) <-> s }
mapping dec_bits_7 : bits(7) <-> string = { dec_bits(7, s) <-> s }
mapping dec_bits_8 : bits(8) <-> string = { dec_bits(8, s) <-> s }
mapping dec_bits_9 : bits(9) <-> string = { dec_bits(9, s) <-> s }
mapping dec_bits_10 : bits(10) <-> string = { dec_bits(10, s) <-> s }
mapping dec_bits_32 : bits(32) <-> string = { dec_bits(32, s) <-> s }

$endif _DEC_BITS
