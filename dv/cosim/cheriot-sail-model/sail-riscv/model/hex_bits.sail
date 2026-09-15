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

$ifndef _HEX_BITS
$define _HEX_BITS

$include <vector.sail>
$include <string.sail>

val "parse_hex_bits" : forall 'n, 'n > 0. (int('n), string) -> bits('n)
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

$endif _HEX_BITS
