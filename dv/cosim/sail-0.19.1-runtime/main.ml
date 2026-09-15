(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Elf_loader;;

let opt_file_arguments = ref ([] : string list)
let opt_raw_files = ref ([] : (string * Nat_big_num.num)  list)
let options = Arg.align [
    ( "-raw",
      Arg.String (fun s ->
      let l = Util.split_on_char '@' s in
      let (file, addr) = match l with
        | [fname;addr] -> (fname, Nat_big_num.of_string addr)
        | _ -> raise (Arg.Bad (s ^ " not of form <filename>@<addr>")) in
      opt_raw_files := (file, addr) :: !opt_raw_files),
      "<file@0xADDR> load a raw binary in memory at given address.");
    ("-cycle-limit", Arg.Set_int (Sail_lib.opt_cycle_limit), "<int> exit after given number of instructions executed.")]

let usage_msg = "Sail OCaml RTS options:"

let () =
  Arg.parse options (fun s -> opt_file_arguments := !opt_file_arguments @ [s]) usage_msg

let rec load_raw_files = function
  | (file, addr) :: files -> begin
      let ic = open_in_bin file in
      let addr' = ref addr in
      try
        while true do
          let b = input_byte ic in
          Sail_lib.wram !addr' b;
          addr' := Nat_big_num.succ !addr';
        done
      with End_of_file -> ();
      load_raw_files files
    end
  | [] -> ()

let () =
  Random.self_init ();
  begin
    match !opt_file_arguments with
    | f :: _ -> load_elf f
    | _ -> ()
  end;
  load_raw_files !opt_raw_files;
  (* ocaml_backend.ml will append from here *)
