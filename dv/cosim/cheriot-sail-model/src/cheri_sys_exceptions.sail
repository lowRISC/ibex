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

/* CHERI exception model */

type ext_exception = unit

/*
 * On traps, EPCC comes to hold PCC verbatim.  Notably, PCC is not sealed under
 * otype_sentry (contrast, for example, CJALR).
 */
function handle_trap_extension(p : Privilege, pc : xlenbits, u : option(unit)) -> unit = {
  match p {
    Machine => {
      let (representable, mepcc) = setCapAddr(PCC, pc);
      // mepcc might be unrepresentable if this is a bounds violation on PCC.
      // In that case PCC should have had the tag cleared in ext_handle_fetch_check_error
      assert(representable | not(mepcc.tag));
      MEPCC   = mepcc
    },
    _ => internal_error(__FILE__, __LINE__,"unsupported")
  }
}

/* used for traps and ECALL */
function prepare_trap_vector(p : Privilege, c : Mcause) -> xlenbits = {
  if p != Machine then internal_error(__FILE__, __LINE__,"unsupported");
  let tcc : Capability = MTCC;
  let v = Mk_Mtvec(tcc.address);
  /* MTCC should have been validated and legalized on write.
   * Only direct mode is supported */
  match (trapVectorMode_of_bits(v[Mode])) {
    TV_Direct => (),
    _         => internal_error(__FILE__, __LINE__, "unsupported trap mode"),
  };
  nextPCC = tcc; 
  tcc.address
}

/*
 * Get the user-visible ?EPC from ?EPCC.  This is not used for control flow,
 * just for reads from (integer) CSRs. EPCC is validated on write
 * so no legalization is required here.
 */
val get_xret_target : Privilege -> xlenbits
function get_xret_target(p) = {
  if p != Machine then internal_error(__FILE__, __LINE__,"unsupported");
  let cap : Capability = MEPCC;
  cap.address
}

/*
 * Setting mepc via CSRW is not supported. MEPCC should be
 * written using CSpecialRW instead.
 */
val set_xret_target : (Privilege, xlenbits) -> xlenbits
function set_xret_target(p, value) = {
  internal_error(__FILE__, __LINE__,"unsupported");
}

/**
 * MEPCC is validated and legalized on write, so this just sets
 * up the new PCC and returns new PC.
 */
val prepare_xret_target : (Privilege) -> xlenbits
function prepare_xret_target(p) = {
  if p != Machine then internal_error(__FILE__, __LINE__,"unsupported");
  let epcc : Capability = MEPCC;
  nextPCC = epcc;
  epcc.address
}

/* other trap-related CSRs */

function get_mtvec() -> xlenbits =
  MTCC.address

function get_stvec() -> xlenbits =
  zeros()

function get_utvec() -> xlenbits =
  zeros()

// CHERIoT uses MTCC instead of mtvec/stvec/utvec.  In RVFI-DII cosim mode
// these writes come from standard startup code that we don't check; accept
// them silently so the model does not abort.
function set_mtvec(value : xlenbits) -> xlenbits = value

function set_stvec(value : xlenbits) -> xlenbits = value

function set_utvec(value : xlenbits) -> xlenbits = value
