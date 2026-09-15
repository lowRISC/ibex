(*=======================================================================================*)
(*  CHERI RISCV Sail Model                                                               *)
(*                                                                                       *)
(*  This CHERI Sail RISC-V architecture model here, comprising all files and             *)
(*  directories except for the snapshots of the Lem and Sail libraries in the            *)
(*  prover_snapshots directory (which include copies of their licenses), is subject      *)
(*  to the BSD two-clause licence below.                                                 *)
(*                                                                                       *)
(*  Copyright (c) 2017-2021                                                              *)
(*    Alasdair Armstrong                                                                 *)
(*    Thomas Bauereiss                                                                   *)
(*    Brian Campbell                                                                     *)
(*    Jessica Clarke                                                                     *)
(*    Nathaniel Wesley Filardo (contributions prior to July 2020, thereafter Microsoft)  *)
(*    Alexandre Joannou                                                                  *)
(*    Microsoft                                                                          *)
(*    Prashanth Mundkur                                                                  *)
(*    Robert Norton-Wright (contributions prior to March 2020, thereafter Microsoft)     *)
(*    Alexander Richardson                                                               *)
(*    Peter Rugg                                                                         *)
(*    Peter Sewell                                                                       *)
(*                                                                                       *)
(*  All rights reserved.                                                                 *)
(*                                                                                       *)
(*  This software was developed by SRI International and the University of               *)
(*  Cambridge Computer Laboratory (Department of Computer Science and                    *)
(*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV"), and                 *)
(*  under DARPA contract HR0011-18-C-0016 ("ECATS") as part of the DARPA                 *)
(*  SSITH research programme.                                                            *)
(*                                                                                       *)
(*  This software was developed within the Rigorous Engineering of                       *)
(*  Mainstream Systems (REMS) project, partly funded by EPSRC grant                      *)
(*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.                        *)
(*                                                                                       *)
(*  This project has received funding from the European Research Council                 *)
(*  (ERC) under the European Union’s Horizon 2020 research and innovation                *)
(*  programme (grant agreement 789108, ELVER).                                           *)
(*                                                                                       *)
(*  Redistribution and use in source and binary forms, with or without                   *)
(*  modification, are permitted provided that the following conditions                   *)
(*  are met:                                                                             *)
(*  1. Redistributions of source code must retain the above copyright                    *)
(*     notice, this list of conditions and the following disclaimer.                     *)
(*  2. Redistributions in binary form must reproduce the above copyright                 *)
(*     notice, this list of conditions and the following disclaimer in                   *)
(*     the documentation and/or other materials provided with the                        *)
(*     distribution.                                                                     *)
(*                                                                                       *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''                   *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED                    *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A                      *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR                  *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,                         *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT                     *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF                     *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND                  *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,                   *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT                   *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF                   *)
(*  SUCH DAMAGE.                                                                         *)
(*=======================================================================================*)

Require Import Sail2_instr_kinds.
Require Import Sail2_values.
Require Import Sail2_operators_mwords.
Require Import Sail2_prompt_monad.
Require Import Sail2_prompt.

Definition write_ram {rv e} wk (addr : mword 64) size (v : mword (8 * size)) (tag : bool) : monad rv bool e := write_memt wk addr size v (bitU_of_bool tag).

Definition read_ram {rv e} rk (addr : mword 64) size (read_tag : bool) `{ArithFact (size >= 0)} : monad rv (mword (8 * size) * bool) e :=
  if read_tag then
    read_memt rk addr size >>= fun '(data, tag) =>
    bool_of_bitU_nondet tag >>= fun tag =>
    returnm (data, tag)
  else
    read_mem rk 64 addr size >>= fun data =>
    returnm (data, false).

Definition write_tag_bool {rv A E} (addr : mword A) tag : monad rv unit E :=
 read_memt Read_plain addr 16 >>= fun '(cap, _) =>
 write_memt Write_plain addr 16 cap (bitU_of_bool tag) >>= (fun _ => returnm tt).

Definition read_tag_bool {rv E} (addr : mword 64) : monad rv bool E :=
  read_memt (B := 128) Read_plain addr 16 >>= fun '(cap, tag) =>
  bool_of_bitU_nondet tag.
