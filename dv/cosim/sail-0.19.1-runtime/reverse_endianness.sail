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

$ifndef _REVERSE_ENDIANNESS
$define _REVERSE_ENDIANNESS

$ifdef _DEFAULT_DEC

$include <vector_dec.sail>

/* reverse_endianness function set up to ensure it generates good SMT
definitions. The concat/extract pattern may be less efficient in other
backends where these are not primitive operations. */

val reverse_endianness : forall 'n, 'n in {8, 16, 32, 64, 128}. bits('n) -> bits('n)

function reverse_endianness(xs) = {
  let len = length(xs);
  if len == 8 then {
    xs
  } else if len == 16 then {
    xs[7 .. 0] @ xs[15 .. 8]
  } else if len == 32 then {
    xs[7 .. 0] @ xs[15 .. 8] @ xs[23 .. 16] @ xs[31 .. 24]
  } else if len == 64 then {
    xs[7 .. 0] @ xs[15 .. 8] @ xs[23 .. 16] @ xs[31 .. 24] @ xs[39 .. 32] @ xs[47 .. 40] @ xs[55 .. 48] @ xs[63 .. 56]
  } else {
    xs[7 .. 0] @ xs[15 .. 8] @ xs[23 .. 16] @ xs[31 .. 24] @ xs[39 .. 32] @ xs[47 .. 40] @ xs[55 .. 48] @ xs[63 .. 56]
    @ xs[71 .. 64] @ xs[79 .. 72] @ xs[87 .. 80] @ xs[95 .. 88] @ xs[103 .. 96] @ xs[111 .. 104] @ xs[119 .. 112] @ xs[127 .. 120]
  }
}

$endif

$endif
