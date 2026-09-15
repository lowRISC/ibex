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

/* CHERI system CSRs */

/* Capability control csr */

bitfield ccsr : xlenbits = {
  d       :  1,      /* dirty  */
  e       :  0       /* enable */
}

register mccsr : ccsr
register sccsr : ccsr
register uccsr : ccsr

/* Stack high water mark registers */
register MSHWMB    : xlenbits
register MSHWM     : xlenbits

/* access to CCSRs */

// for now, use a single privilege-independent legalizer
function legalize_ccsr(c : ccsr, v : xlenbits) -> ccsr = {
  // write only the defined bits, leaving the other bits untouched
  // Technically, WPRI does not need a legalizer, since software is
  // assumed to legalize; so we could remove this function.
  let v = Mk_ccsr(v);
  /* For now these bits are not really supported so hardwired to true */
  let c = update_d(c, 0b1);
  let c = update_e(c, 0b1);
  c
}

/*!
 * Legalize stack high water mark by rounding
 * down to 16-byte aligned value.
 */
function legalize_mshwm(v : xlenbits) -> xlenbits = {
  [v with 3..0=0x0]
}

// XXX these are currently disabled due to sail bug when compiling C
//mapping clause csr_name_map = 0x8c0 <-> "uccsr"
//mapping clause csr_name_map = 0x9c0 <-> "sccsr"
//mapping clause csr_name_map = 0xBc0 <-> "mccsr"

function clause ext_read_CSR (0x8C0) = Some(uccsr.bits())
function clause ext_read_CSR (0x9C0) = Some(sccsr.bits())
function clause ext_read_CSR (0xBC0) = Some(mccsr.bits())

function clause ext_read_CSR (0xBC1) = Some(MSHWM)
function clause ext_read_CSR (0xBC2) = Some(MSHWMB)

function clause ext_write_CSR (0x8C0, value) = { uccsr = legalize_ccsr(uccsr, value); Some(uccsr.bits()) }
function clause ext_write_CSR (0x9C0, value) = { sccsr = legalize_ccsr(sccsr, value); Some(sccsr.bits()) }
function clause ext_write_CSR (0xBC0, value) = { mccsr = legalize_ccsr(mccsr, value); Some(mccsr.bits()) }

function clause ext_write_CSR (0xBC1, value) = { MSHWM  = legalize_mshwm(value); Some(MSHWM) }
function clause ext_write_CSR (0xBC2, value) = { MSHWMB = legalize_mshwm(value); Some(MSHWMB) }

function clause ext_is_CSR_defined (0x8C0, p) = haveUsrMode()  // uccsr
function clause ext_is_CSR_defined (0x9C0, p) = haveSupMode() & (p == Machine | p == Supervisor) // sccsr
function clause ext_is_CSR_defined (0xBC0, p) = p == Machine | p == Supervisor // mccsr

function clause ext_is_CSR_defined (0xBC1, Machine) = true // MSHWM
function clause ext_is_CSR_defined (0xBC2, Machine) = true // MSHWMB

/* Other architectural registers */

register PCC       : Capability
register nextPCC   : Capability
register MTCC      : Capability
register MTDC      : Capability
register MScratchC : Capability
register MEPCC     : Capability

/* Cheri PCC helpers */

function min_instruction_bytes () -> CapAddrInt = {
  if   (~ (sys_enable_writable_misa ())) & (~ (sys_enable_rvc ()))
  then 4  /* RVC is hardwired to be disabled */
  else 2  /* RVC is active or it could become active */
}

/* Checking whether the Xcheri extension is enabled */

function haveXcheri () -> bool =
  /* This is a necessary but not sufficient condition, but should do for now. */
  misa.X() == 0b1
