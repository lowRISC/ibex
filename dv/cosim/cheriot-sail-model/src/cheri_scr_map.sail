/*=======================================================================================*/
/*  CHERI RISCV Sail Model                                                               */
/*                                                                                       */
/*  This CHERI Sail RISC-V architecture model here, comprising all files and             */
/*  directories except for the snapshots of the Lem and Sail libraries in the            */
/*  prover_snapshots directory (which include copies of their licenses), is subject      */
/*  to the BSD two-clause licence below.                                                 */
/*                                                                                       */
/*  Copyright (c) 2017-2021                                                              */
/*    Alasdair Armstrong                                                                 */
/*    Thomas Bauereiss                                                                   */
/*    Brian Campbell                                                                     */
/*    Jessica Clarke                                                                     */
/*    Nathaniel Wesley Filardo (contributions prior to July 2020, thereafter Microsoft)  */
/*    Alexandre Joannou                                                                  */
/*    Microsoft                                                                          */
/*    Prashanth Mundkur                                                                  */
/*    Robert Norton-Wright (contributions prior to March 2020, thereafter Microsoft)     */
/*    Alexander Richardson                                                               */
/*    Peter Rugg                                                                         */
/*    Peter Sewell                                                                       */
/*                                                                                       */
/*  All rights reserved.                                                                 */
/*                                                                                       */
/*  This software was developed by SRI International and the University of               */
/*  Cambridge Computer Laboratory (Department of Computer Science and                    */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 */
/*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 */
/*  SSITH research programme.                                                            */
/*                                                                                       */
/*  This software was developed within the Rigorous Engineering of                       */
/*  Mainstream Systems (REMS) project, partly funded by EPSRC grant                      */
/*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.                        */
/*                                                                                       */
/*  This project has received funding from the European Research Council                 */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation                */
/*  programme (grant agreement 789108, ELVER).                                           */
/*                                                                                       */
/*  Redistribution and use in source and binary forms, with or without                   */
/*  modification, are permitted provided that the following conditions                   */
/*  are met:                                                                             */
/*  1. Redistributions of source code must retain the above copyright                    */
/*     notice, this list of conditions and the following disclaimer.                     */
/*  2. Redistributions in binary form must reproduce the above copyright                 */
/*     notice, this list of conditions and the following disclaimer in                   */
/*     the documentation and/or other materials provided with the                        */
/*     distribution.                                                                     */
/*                                                                                       */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   */
/*  SUCH DAMAGE.                                                                         */
/*=======================================================================================*/

/* Mapping of scr addresses to their names. */

val scr_name_map : screg <-> string

scattered mapping scr_name_map

mapping clause scr_name_map = 0b00000 <-> "pcc"
mapping clause scr_name_map = 0b00001 <-> "ddc"

mapping clause scr_name_map = 0b00100 <-> "utcc"
mapping clause scr_name_map = 0b00101 <-> "utdc"
mapping clause scr_name_map = 0b00110 <-> "uscratchc"
mapping clause scr_name_map = 0b00111 <-> "uepcc"

mapping clause scr_name_map = 0b10100 <-> "stcc"
mapping clause scr_name_map = 0b10101 <-> "stdc"
mapping clause scr_name_map = 0b10110 <-> "sscratchc"
mapping clause scr_name_map = 0b10111 <-> "sepcc"

mapping clause scr_name_map = 0b11100 <-> "mtcc"
mapping clause scr_name_map = 0b11101 <-> "mtdc"
mapping clause scr_name_map = 0b11110 <-> "mscratchc"
mapping clause scr_name_map = 0b11111 <-> "mepcc"
// XXX: the following appears to trigger a C code generator bug:
// error: implicit declaration of function 'hex_bits_5_matches_prefix' is invalid in C99
// mapping clause scr_name_map = screg   <-> hex_bits_5(screg)
mapping clause scr_name_map = 0b00010 <-> "0x2"
mapping clause scr_name_map = 0b00011 <-> "0x3"
mapping clause scr_name_map = 0b01000 <-> "0x8"
mapping clause scr_name_map = 0b01001 <-> "0x9"
mapping clause scr_name_map = 0b01010 <-> "0xA"
mapping clause scr_name_map = 0b01011 <-> "0xB"
mapping clause scr_name_map = 0b01100 <-> "0xC"
mapping clause scr_name_map = 0b01101 <-> "0xD"
mapping clause scr_name_map = 0b01110 <-> "0xE"
mapping clause scr_name_map = 0b01111 <-> "0xF"
mapping clause scr_name_map = 0b10000 <-> "0x10"
mapping clause scr_name_map = 0b10001 <-> "0x11"
mapping clause scr_name_map = 0b10010 <-> "0x12"
mapping clause scr_name_map = 0b10011 <-> "0x13"
mapping clause scr_name_map = 0b11000 <-> "0x18"
mapping clause scr_name_map = 0b11001 <-> "0x19"
mapping clause scr_name_map = 0b11010 <-> "0x1A"
mapping clause scr_name_map = 0b11011 <-> "0x1B"

val scr_name : screg -> string
overload to_str = {scr_name}
