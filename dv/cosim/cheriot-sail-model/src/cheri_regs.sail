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

/* accessors for capability representation */

$ifdef RVFI_DII
val rvfi_rC : forall 'n, 0 <= 'n < 32. (regno('n), regor, CapBits, bool) -> unit
function rvfi_rC (r,o,v,t) = {
  if (o == rs_1) then {
    rvfi_cheri_data[rvfi_cs1_addr]  = to_bits(8,r);
    rvfi_cheri_data[rvfi_cs1_rdata] = zero_extend(v);
    rvfi_cheri_data[rvfi_cs1_rtag]  = to_bits(8, if t then 1 else 0);
  };
  if (o == rs_2) then {
    rvfi_cheri_data[rvfi_cs2_addr]  = to_bits(8,r);
    rvfi_cheri_data[rvfi_cs2_rdata] = zero_extend(v);
    rvfi_cheri_data[rvfi_cs2_rtag]  = to_bits(8, if t then 1 else 0);
  };
  rvfi_cheri_data_present = true;
}
$else
val rvfi_rC : forall 'n, 0 <= 'n < 32. (regno('n), bool, CapBits, bool) -> unit
function rvfi_rC (r,o,v,t) = ()
$endif

/* reads a given capability register, or the null capability if the argument is zero. */
val rC : forall 'n, 0 <= 'n < 32. (regno('n), regor) -> regtype effect {rreg, escape}
function rC (r,o) = {
  let v : Capability =
    match r {
      0  => zero_reg,
      1  => x1,
      2  => x2,
      3  => x3,
      4  => x4,
      5  => x5,
      6  => x6,
      7  => x7,
      8  => x8,
      9  => x9,
      10 => x10,
      11 => x11,
      12 => x12,
      13 => x13,
      14 => x14,
      15 => x15,
      _  => throw Error_not_rv32e_register()
    };
  if (r != 0) then {
    rvfi_rC(r, o, capToBits(v), v.tag);
  };
  v
}

$ifdef RVFI_DII
val rvfi_wC : forall 'n, 0 <= 'n < 32. (regno('n), CapBits, bool) -> unit
function rvfi_wC (r,v,t) = {
  rvfi_cheri_data[rvfi_cd_addr] = to_bits(8,r);
  rvfi_cheri_data[rvfi_cd_wdata] = zero_extend(v);
  rvfi_cheri_data[rvfi_cd_wtag] = to_bits(8, if t then 1 else 0);
  rvfi_cheri_data_present = true;
}
$else
val rvfi_wC : forall 'n, 0 <= 'n < 32. (regno('n), CapBits, bool) -> unit
function rvfi_wC (r,v,t) = ()
$endif

/* writes a register with a capability value */
val wC : forall 'n, 0 <= 'n < 32. (regno('n), regtype) -> unit
function wC (r, v) = {
  /* Encode and decode capability to normalise it prior to writing to register */
  let v = encCapabilityToCapability(v.tag, capToEncCap(v));
  match r {
    0  => (),
    1  => x1 = v,
    2  => x2 = v,
    3  => x3 = v,
    4  => x4 = v,
    5  => x5 = v,
    6  => x6 = v,
    7  => x7 = v,
    8  => x8 = v,
    9  => x9 = v,
    10 => x10 = v,
    11 => x11 = v,
    12 => x12 = v,
    13 => x13 = v,
    14 => x14 = v,
    15 => x15 = v,
    _  => throw Error_not_rv32e_register()
  };
  if (r != 0) then {
     rvfi_wC(r, capToBits(v), v.tag);
     if get_config_print_reg() then
       print_reg("c" ^ dec_str(r) ^ " <- " ^ RegStr(v));
  }
}

function rC_bits(r: bits(5), o: regor) -> regtype = rC(unsigned(r), o)

function wC_bits(r: bits(5), v: regtype) -> unit = wC(unsigned(r), v)

overload C = {rC_bits, wC_bits, rC, wC}

val ext_init_regs : unit -> unit
function ext_init_regs () = {
  PCC = root_cap_exe;
  nextPCC = root_cap_exe;

  MTCC = root_cap_exe;
  MTDC = root_cap_mem;
  MScratchC = root_cap_seal;
  MEPCC = root_cap_exe;

  x1  = null_cap;
  x2  = null_cap;
  x3  = null_cap;
  x4  = null_cap;
  x5  = null_cap;
  x6  = null_cap;
  x7  = null_cap;
  x8  = null_cap;
  x9  = null_cap;
  x10 = null_cap;
  x11 = null_cap;
  x12 = null_cap;
  x13 = null_cap;
  x14 = null_cap;
  x15 = null_cap;

  misa->X() = 0b1;
  misa->B() = 0b1; /* TODO this ought to be set by base model? */
  mccsr->d() = 0b1;
  mccsr->e() = 0b1;
  sccsr->d() = 0b1;
  sccsr->e() = 0b1;
  uccsr->d() = 0b1;
  uccsr->e() = 0b1;
}

/*!
 * This function is called after above when running rvfi and allows the model
 * to be initialised differently. For RVFI we initialise cap regs to default
 * instead of null.
 */
val ext_rvfi_init : unit -> unit
function ext_rvfi_init () = {
  x1  = root_cap_mem;
  x2  = root_cap_mem;
  x3  = root_cap_mem;
  x4  = root_cap_mem;
  x5  = root_cap_mem;
  x6  = root_cap_mem;
  x7  = root_cap_mem;
  x8  = root_cap_mem;
  x9  = root_cap_mem;
  x10 = root_cap_mem;
  x11 = root_cap_mem;
  x12 = root_cap_mem;
  x13 = root_cap_mem;
  x14 = root_cap_mem;
  x15 = root_cap_mem;
}

/* register names */

val cap_reg_name_abi : regidx -> string

function cap_reg_name_abi(r) = {
  match (r) {
    0b00000 => "cnull",
    _       => "c" ^ reg_name_abi(r)
  }
}

overload to_str = {cap_reg_name_abi}

/* mappings for assembly */

val cap_reg_name : bits(5) <-> string
mapping cap_reg_name = {
    0b00000 <-> "cnull",
    r       <-> "c" ^ reg_name(r)
}

mapping cap_creg_name : bits(3) <-> string = {
  r <-> "c" ^ creg_name(r)
}

function string_of_capreg_idx(reg : capreg_idx) -> string =
  match reg {
    0b0 @ greg : bits(5) => "c" ^ dec_str(unsigned(greg)) ^ "/" ^ cap_reg_name_abi(greg),
    0b100000 => "PCC",
    0b111100 => "MTCC",
    0b111101 => "MTDC",
    0b111110 => "MScratchC",
    0b111111 => "EPCC",
    _        => "Unknown/" ^ BitStr(reg),
  }
