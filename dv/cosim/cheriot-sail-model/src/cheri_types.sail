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

let otype_unsealed  = 0
let otype_sentry    = 1 /* Sealed erstwhile or prospective PCC */
let otype_sentry_id = 2 /* sentry disabling interrupts */
let otype_sentry_ie = 3 /* sentry enabling interrupts */
let otype_sentry_bid = 4 /* backward sentry disabling interrupts */
let otype_sentry_bie = 5 /* backward sentry enabling interrupts */

enum CPtrCmpOp = {
  CEQ,
  CNE,
  CLT,
  CLE,
  CLTU,
  CLEU,
  CEXEQ,
  CNEXEQ
}

enum ClearRegSet = {
  GPRegs,
  FPRegs
}

enum CapEx = {
  CapEx_None,
  CapEx_BoundsViolation,
  CapEx_TagViolation,
  CapEx_SealViolation,
  CapEx_TypeViolation,
  CapEx_UserDefViolation,
  CapEx_UnalignedBase,
  CapEx_GlobalViolation,
  CapEx_PermitExecuteViolation,
  CapEx_PermitLoadViolation,
  CapEx_PermitStoreViolation,
  CapEx_PermitLoadCapViolation,
  CapEx_PermitStoreCapViolation,
  CapEx_AccessSystemRegsViolation,
  CapEx_PermitCInvokeViolation,
  CapEx_PermitSetCIDViolation
}

function CapExCode(ex) : CapEx -> bits(5) =
  match ex {
    CapEx_None                          => 0b00000,
    CapEx_BoundsViolation               => 0b00001,
    CapEx_TagViolation                  => 0b00010,
    CapEx_SealViolation                 => 0b00011,
    CapEx_TypeViolation                 => 0b00100,
    CapEx_UserDefViolation              => 0b01000,
    CapEx_UnalignedBase                 => 0b01011,
    CapEx_GlobalViolation               => 0b10000,
    CapEx_PermitExecuteViolation        => 0b10001,
    CapEx_PermitLoadViolation           => 0b10010,
    CapEx_PermitStoreViolation          => 0b10011,
    CapEx_PermitLoadCapViolation        => 0b10100,
    CapEx_PermitStoreCapViolation       => 0b10101,
    CapEx_AccessSystemRegsViolation     => 0b11000,
    CapEx_PermitCInvokeViolation        => 0b11001,
    CapEx_PermitSetCIDViolation         => 0b11100
  }

function string_of_capex (ex) : CapEx -> string =
  match ex {
    CapEx_None                          => "None"                        ,
    CapEx_BoundsViolation               => "BoundsViolation"             ,
    CapEx_TagViolation                  => "TagViolation"                ,
    CapEx_SealViolation                 => "SealViolation"               ,
    CapEx_TypeViolation                 => "TypeViolation"               ,
    CapEx_UserDefViolation              => "UserDefViolation"            ,
    CapEx_UnalignedBase                 => "UnalignedBounds"             ,
    CapEx_GlobalViolation               => "GlobalViolation"             ,
    CapEx_PermitExecuteViolation        => "PermitExecuteViolation"      ,
    CapEx_PermitLoadViolation           => "PermitLoadViolation"         ,
    CapEx_PermitStoreViolation          => "PermitStoreViolation"        ,
    CapEx_PermitLoadCapViolation        => "PermitLoadCapViolation"      ,
    CapEx_PermitStoreCapViolation       => "PermitStoreCapViolation"     ,
    CapEx_AccessSystemRegsViolation     => "AccessSystemRegsViolation"   ,
    CapEx_PermitCInvokeViolation        => "PermitCInvokeViolation"      ,
    CapEx_PermitSetCIDViolation         => "PermitSetCIDViolation"
  }

type capreg_idx = bits(6)
let PCC_IDX : capreg_idx = 0b100000
let DDC_IDX : capreg_idx = 0b100001
let CGP_IDX : bits(5) = 0b00011

type screg = bits(5)
