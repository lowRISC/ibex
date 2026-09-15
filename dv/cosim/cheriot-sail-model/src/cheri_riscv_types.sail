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

/*
 * Extension for CHERI page table walker
 *
 * We are going to carry around a summary of the PTW walk for data-dependent
 * (well, tag-dependent) behaviors by the instructions.
 */

enum ext_ptw_lc = {
  /* Tags flow as might be expected */
  PTW_LC_OK,

  /* PTE settings require clearing tags */
  PTW_LC_CLEAR
}

enum ext_ptw_sc = {
  /* Tag stores are permitted */
  PTW_SC_OK,

  /* Tag-asserting stores trap */
  PTW_SC_TRAP
}

struct ext_ptw = {
  ptw_lc : ext_ptw_lc,
  ptw_sc : ext_ptw_sc
}

function ext_ptw_lc_join(e : ext_ptw, l : ext_ptw_lc) -> ext_ptw =
  { e with ptw_lc =
      match l {
        PTW_LC_OK => e.ptw_lc,
        PTW_LC_CLEAR => l
      }
  }

function ext_ptw_sc_join(e : ext_ptw, s : ext_ptw_sc) -> ext_ptw =
  { e with ptw_sc =
      match s {
        PTW_SC_OK => e.ptw_sc,
        PTW_SC_TRAP => s
      }
  }

/* initial value of the PTW accumulator */
let init_ext_ptw : ext_ptw = struct {
  ptw_lc = PTW_LC_OK,
  ptw_sc = PTW_SC_OK
}

/* Address translation failures */
enum ext_ptw_fail = {
  EPTWF_NO_PERM,
  EPTWF_CAP_ERR
}

/* Address translation errors */
enum ext_ptw_error = {AT_CAP_ERR}

/* CHERI exception extensions */

enum ext_exc_type = {
  EXC_LOAD_CAP_PAGE_FAULT,
  EXC_SAMO_CAP_PAGE_FAULT,
  EXC_CHERI
}

/* CHERI conversion of extension exceptions to bits */
val ext_exc_type_to_bits : ext_exc_type -> exc_code
function ext_exc_type_to_bits(e) =
  match (e) {
    EXC_LOAD_CAP_PAGE_FAULT => 0x1a,
    EXC_SAMO_CAP_PAGE_FAULT => 0x1b,
    EXC_CHERI               => 0x1c
  }

/* CHERI conversion of extension exceptions to integers */
val num_of_ext_exc_type : ext_exc_type -> {'n, (0 <= 'n < xlen). int('n)}
function num_of_ext_exc_type(e) =
  match (e) {
    EXC_LOAD_CAP_PAGE_FAULT => 26,
    EXC_SAMO_CAP_PAGE_FAULT => 27,
    EXC_CHERI               => 28
  }

/* CHERI conversion of extension exceptions to strings */
val ext_exc_type_to_str : ext_exc_type -> string
function ext_exc_type_to_str(e) =
  match (e) {
    EXC_LOAD_CAP_PAGE_FAULT => "load-cap-page-fault",
    EXC_SAMO_CAP_PAGE_FAULT => "store/amo-cap-page-fault",
    EXC_CHERI               => "cheri"
  }
