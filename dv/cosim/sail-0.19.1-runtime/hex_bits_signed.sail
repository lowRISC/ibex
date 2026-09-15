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

$ifndef _HEX_BITS_SIGNED
$define _HEX_BITS_SIGNED

$include <vector.sail>
$include <option.sail>
$include <mapping.sail>
$include <hex_bits.sail>

val hex_bits_signed : forall 'n, 'n > 0. bits('n) <-> (int('n), string)

function hex_bits_signed_forwards(bv) = {
  let len = length(bv);
  let s = if bv[len - 1] == bitone then {
    concat_str("-", hex_str(unsigned(not_vec(bv)) + 1))
  } else {
    hex_str(unsigned(bv))
  };
  (length(bv), s)
}

function hex_bits_signed_forwards_matches(bv) = true

function hex_bits_signed_backwards(n, str) = {
  if string_take(str, 1) == "-" then {
    sub_bits(sail_zeros(n), parse_hex_bits(n, string_drop(str, 1)))
  } else {
    let parsed = parse_hex_bits(n, str);
    if parsed[n - 1] == bitzero then {
      parsed
    } else {
      sail_zeros(n)
    }
  }
}

function hex_bits_signed_backwards_matches(n, str) = {
  if string_take(str, 1) == "-" then {
    valid_hex_bits(n, string_drop(str, 1))
  } else if valid_hex_bits(n, str) then {
    let parsed = parse_hex_bits(n, str);
    parsed[n - 1] == bitzero
  } else {
    false
  }
}

mapping hex_bits_signed_1 : bits(1) <-> string = { hex_bits_signed(1, s) <-> s }
mapping hex_bits_signed_2 : bits(2) <-> string = { hex_bits_signed(2, s) <-> s }
mapping hex_bits_signed_3 : bits(3) <-> string = { hex_bits_signed(3, s) <-> s }
mapping hex_bits_signed_4 : bits(4) <-> string = { hex_bits_signed(4, s) <-> s }
mapping hex_bits_signed_5 : bits(5) <-> string = { hex_bits_signed(5, s) <-> s }
mapping hex_bits_signed_6 : bits(6) <-> string = { hex_bits_signed(6, s) <-> s }
mapping hex_bits_signed_7 : bits(7) <-> string = { hex_bits_signed(7, s) <-> s }
mapping hex_bits_signed_8 : bits(8) <-> string = { hex_bits_signed(8, s) <-> s }
mapping hex_bits_signed_9 : bits(9) <-> string = { hex_bits_signed(9, s) <-> s }

mapping hex_bits_signed_10 : bits(10) <-> string = { hex_bits_signed(10, s) <-> s }
mapping hex_bits_signed_11 : bits(11) <-> string = { hex_bits_signed(11, s) <-> s }
mapping hex_bits_signed_12 : bits(12) <-> string = { hex_bits_signed(12, s) <-> s }
mapping hex_bits_signed_13 : bits(13) <-> string = { hex_bits_signed(13, s) <-> s }
mapping hex_bits_signed_14 : bits(14) <-> string = { hex_bits_signed(14, s) <-> s }
mapping hex_bits_signed_15 : bits(15) <-> string = { hex_bits_signed(15, s) <-> s }
mapping hex_bits_signed_16 : bits(16) <-> string = { hex_bits_signed(16, s) <-> s }
mapping hex_bits_signed_17 : bits(17) <-> string = { hex_bits_signed(17, s) <-> s }
mapping hex_bits_signed_18 : bits(18) <-> string = { hex_bits_signed(18, s) <-> s }
mapping hex_bits_signed_19 : bits(19) <-> string = { hex_bits_signed(19, s) <-> s }

mapping hex_bits_signed_20 : bits(20) <-> string = { hex_bits_signed(20, s) <-> s }
mapping hex_bits_signed_21 : bits(21) <-> string = { hex_bits_signed(21, s) <-> s }
mapping hex_bits_signed_22 : bits(22) <-> string = { hex_bits_signed(22, s) <-> s }
mapping hex_bits_signed_23 : bits(23) <-> string = { hex_bits_signed(23, s) <-> s }
mapping hex_bits_signed_24 : bits(24) <-> string = { hex_bits_signed(24, s) <-> s }
mapping hex_bits_signed_25 : bits(25) <-> string = { hex_bits_signed(25, s) <-> s }
mapping hex_bits_signed_26 : bits(26) <-> string = { hex_bits_signed(26, s) <-> s }
mapping hex_bits_signed_27 : bits(27) <-> string = { hex_bits_signed(27, s) <-> s }
mapping hex_bits_signed_28 : bits(28) <-> string = { hex_bits_signed(28, s) <-> s }
mapping hex_bits_signed_29 : bits(29) <-> string = { hex_bits_signed(29, s) <-> s }

mapping hex_bits_signed_30 : bits(30) <-> string = { hex_bits_signed(30, s) <-> s }
mapping hex_bits_signed_31 : bits(31) <-> string = { hex_bits_signed(31, s) <-> s }
mapping hex_bits_signed_32 : bits(32) <-> string = { hex_bits_signed(32, s) <-> s }
mapping hex_bits_signed_33 : bits(33) <-> string = { hex_bits_signed(33, s) <-> s }
mapping hex_bits_signed_34 : bits(34) <-> string = { hex_bits_signed(34, s) <-> s }
mapping hex_bits_signed_35 : bits(35) <-> string = { hex_bits_signed(35, s) <-> s }
mapping hex_bits_signed_36 : bits(36) <-> string = { hex_bits_signed(36, s) <-> s }
mapping hex_bits_signed_37 : bits(37) <-> string = { hex_bits_signed(37, s) <-> s }
mapping hex_bits_signed_38 : bits(38) <-> string = { hex_bits_signed(38, s) <-> s }
mapping hex_bits_signed_39 : bits(39) <-> string = { hex_bits_signed(39, s) <-> s }

mapping hex_bits_signed_40 : bits(40) <-> string = { hex_bits_signed(40, s) <-> s }
mapping hex_bits_signed_41 : bits(41) <-> string = { hex_bits_signed(41, s) <-> s }
mapping hex_bits_signed_42 : bits(42) <-> string = { hex_bits_signed(42, s) <-> s }
mapping hex_bits_signed_43 : bits(43) <-> string = { hex_bits_signed(43, s) <-> s }
mapping hex_bits_signed_44 : bits(44) <-> string = { hex_bits_signed(44, s) <-> s }
mapping hex_bits_signed_45 : bits(45) <-> string = { hex_bits_signed(45, s) <-> s }
mapping hex_bits_signed_46 : bits(46) <-> string = { hex_bits_signed(46, s) <-> s }
mapping hex_bits_signed_47 : bits(47) <-> string = { hex_bits_signed(47, s) <-> s }
mapping hex_bits_signed_48 : bits(48) <-> string = { hex_bits_signed(48, s) <-> s }
mapping hex_bits_signed_49 : bits(49) <-> string = { hex_bits_signed(49, s) <-> s }

mapping hex_bits_signed_50 : bits(50) <-> string = { hex_bits_signed(50, s) <-> s }
mapping hex_bits_signed_51 : bits(51) <-> string = { hex_bits_signed(51, s) <-> s }
mapping hex_bits_signed_52 : bits(52) <-> string = { hex_bits_signed(52, s) <-> s }
mapping hex_bits_signed_53 : bits(53) <-> string = { hex_bits_signed(53, s) <-> s }
mapping hex_bits_signed_54 : bits(54) <-> string = { hex_bits_signed(54, s) <-> s }
mapping hex_bits_signed_55 : bits(55) <-> string = { hex_bits_signed(55, s) <-> s }
mapping hex_bits_signed_56 : bits(56) <-> string = { hex_bits_signed(56, s) <-> s }
mapping hex_bits_signed_57 : bits(57) <-> string = { hex_bits_signed(57, s) <-> s }
mapping hex_bits_signed_58 : bits(58) <-> string = { hex_bits_signed(58, s) <-> s }
mapping hex_bits_signed_59 : bits(59) <-> string = { hex_bits_signed(59, s) <-> s }

mapping hex_bits_signed_60 : bits(60) <-> string = { hex_bits_signed(60, s) <-> s }
mapping hex_bits_signed_61 : bits(61) <-> string = { hex_bits_signed(61, s) <-> s }
mapping hex_bits_signed_62 : bits(62) <-> string = { hex_bits_signed(62, s) <-> s }
mapping hex_bits_signed_63 : bits(63) <-> string = { hex_bits_signed(63, s) <-> s }
mapping hex_bits_signed_64 : bits(64) <-> string = { hex_bits_signed(64, s) <-> s }

$endif
