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

$ifndef _HEX_BITS
$define _HEX_BITS

$include <option.sail>
$include <vector.sail>
$include <string.sail>

$[sv_function { types = "int #0" }]
val "parse_hex_bits" : forall 'n, 'n > 0. (int('n), string) -> bits('n)

$[sv_function { types = "int #0" }]
val "valid_hex_bits" : forall 'n, 'n > 0. (int('n), string) -> bool

val hex_bits : forall 'n, 'n > 0. bits('n) <-> (int('n), string)

function hex_bits_forwards(bv) = (length(bv), hex_str(unsigned(bv)))
function hex_bits_forwards_matches(bv) = true

function hex_bits_backwards(n, str) = parse_hex_bits(n, str)
function hex_bits_backwards_matches(n, str) = valid_hex_bits(n, str)

mapping hex_bits_1 : bits(1) <-> string = { hex_bits(1, s) <-> s }
mapping hex_bits_2 : bits(2) <-> string = { hex_bits(2, s) <-> s }
mapping hex_bits_3 : bits(3) <-> string = { hex_bits(3, s) <-> s }
mapping hex_bits_4 : bits(4) <-> string = { hex_bits(4, s) <-> s }
mapping hex_bits_5 : bits(5) <-> string = { hex_bits(5, s) <-> s }
mapping hex_bits_6 : bits(6) <-> string = { hex_bits(6, s) <-> s }
mapping hex_bits_7 : bits(7) <-> string = { hex_bits(7, s) <-> s }
mapping hex_bits_8 : bits(8) <-> string = { hex_bits(8, s) <-> s }
mapping hex_bits_9 : bits(9) <-> string = { hex_bits(9, s) <-> s }

mapping hex_bits_10 : bits(10) <-> string = { hex_bits(10, s) <-> s }
mapping hex_bits_11 : bits(11) <-> string = { hex_bits(11, s) <-> s }
mapping hex_bits_12 : bits(12) <-> string = { hex_bits(12, s) <-> s }
mapping hex_bits_13 : bits(13) <-> string = { hex_bits(13, s) <-> s }
mapping hex_bits_14 : bits(14) <-> string = { hex_bits(14, s) <-> s }
mapping hex_bits_15 : bits(15) <-> string = { hex_bits(15, s) <-> s }
mapping hex_bits_16 : bits(16) <-> string = { hex_bits(16, s) <-> s }
mapping hex_bits_17 : bits(17) <-> string = { hex_bits(17, s) <-> s }
mapping hex_bits_18 : bits(18) <-> string = { hex_bits(18, s) <-> s }
mapping hex_bits_19 : bits(19) <-> string = { hex_bits(19, s) <-> s }

mapping hex_bits_20 : bits(20) <-> string = { hex_bits(20, s) <-> s }
mapping hex_bits_21 : bits(21) <-> string = { hex_bits(21, s) <-> s }
mapping hex_bits_22 : bits(22) <-> string = { hex_bits(22, s) <-> s }
mapping hex_bits_23 : bits(23) <-> string = { hex_bits(23, s) <-> s }
mapping hex_bits_24 : bits(24) <-> string = { hex_bits(24, s) <-> s }
mapping hex_bits_25 : bits(25) <-> string = { hex_bits(25, s) <-> s }
mapping hex_bits_26 : bits(26) <-> string = { hex_bits(26, s) <-> s }
mapping hex_bits_27 : bits(27) <-> string = { hex_bits(27, s) <-> s }
mapping hex_bits_28 : bits(28) <-> string = { hex_bits(28, s) <-> s }
mapping hex_bits_29 : bits(29) <-> string = { hex_bits(29, s) <-> s }

mapping hex_bits_30 : bits(30) <-> string = { hex_bits(30, s) <-> s }
mapping hex_bits_31 : bits(31) <-> string = { hex_bits(31, s) <-> s }
mapping hex_bits_32 : bits(32) <-> string = { hex_bits(32, s) <-> s }
mapping hex_bits_33 : bits(33) <-> string = { hex_bits(33, s) <-> s }
mapping hex_bits_34 : bits(34) <-> string = { hex_bits(34, s) <-> s }
mapping hex_bits_35 : bits(35) <-> string = { hex_bits(35, s) <-> s }
mapping hex_bits_36 : bits(36) <-> string = { hex_bits(36, s) <-> s }
mapping hex_bits_37 : bits(37) <-> string = { hex_bits(37, s) <-> s }
mapping hex_bits_38 : bits(38) <-> string = { hex_bits(38, s) <-> s }
mapping hex_bits_39 : bits(39) <-> string = { hex_bits(39, s) <-> s }

mapping hex_bits_40 : bits(40) <-> string = { hex_bits(40, s) <-> s }
mapping hex_bits_41 : bits(41) <-> string = { hex_bits(41, s) <-> s }
mapping hex_bits_42 : bits(42) <-> string = { hex_bits(42, s) <-> s }
mapping hex_bits_43 : bits(43) <-> string = { hex_bits(43, s) <-> s }
mapping hex_bits_44 : bits(44) <-> string = { hex_bits(44, s) <-> s }
mapping hex_bits_45 : bits(45) <-> string = { hex_bits(45, s) <-> s }
mapping hex_bits_46 : bits(46) <-> string = { hex_bits(46, s) <-> s }
mapping hex_bits_47 : bits(47) <-> string = { hex_bits(47, s) <-> s }
mapping hex_bits_48 : bits(48) <-> string = { hex_bits(48, s) <-> s }
mapping hex_bits_49 : bits(49) <-> string = { hex_bits(49, s) <-> s }

mapping hex_bits_50 : bits(50) <-> string = { hex_bits(50, s) <-> s }
mapping hex_bits_51 : bits(51) <-> string = { hex_bits(51, s) <-> s }
mapping hex_bits_52 : bits(52) <-> string = { hex_bits(52, s) <-> s }
mapping hex_bits_53 : bits(53) <-> string = { hex_bits(53, s) <-> s }
mapping hex_bits_54 : bits(54) <-> string = { hex_bits(54, s) <-> s }
mapping hex_bits_55 : bits(55) <-> string = { hex_bits(55, s) <-> s }
mapping hex_bits_56 : bits(56) <-> string = { hex_bits(56, s) <-> s }
mapping hex_bits_57 : bits(57) <-> string = { hex_bits(57, s) <-> s }
mapping hex_bits_58 : bits(58) <-> string = { hex_bits(58, s) <-> s }
mapping hex_bits_59 : bits(59) <-> string = { hex_bits(59, s) <-> s }

mapping hex_bits_60 : bits(60) <-> string = { hex_bits(60, s) <-> s }
mapping hex_bits_61 : bits(61) <-> string = { hex_bits(61, s) <-> s }
mapping hex_bits_62 : bits(62) <-> string = { hex_bits(62, s) <-> s }
mapping hex_bits_63 : bits(63) <-> string = { hex_bits(63, s) <-> s }
mapping hex_bits_64 : bits(64) <-> string = { hex_bits(64, s) <-> s }

$endif _HEX_BITS
