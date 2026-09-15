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

/* Error handlers for address check errors */

/*!
 * Causes the processor to raise a capability exception by writing the given
 * capability exception cause and a 6-bit register number to the xtval register
 * then signalling an exception. If bit 5 of the register number is set then
 * bits 0-4 refer to the index of a special capability register, otherwise
 * they refer to a general purpose register.
 */
val handle_cheri_cap_exception : (CapEx, capreg_idx) -> unit
function handle_cheri_cap_exception(capEx, regnum) =
  {
    if get_config_print_instr() | get_config_print_exception()
    then print_string("CHERI ", string_of_capex(capEx) ^ " Reg=" ^ string_of_capreg_idx(regnum) ^ " PC=" ^ BitStr(PC));
    let t : sync_exception = struct {
      trap    = E_Extension(EXC_CHERI),
      excinfo = Some(zero_extend(regnum @ CapExCode(capEx)) : xlenbits),
      ext     = None()
    };
    set_next_pc(exception_handler(cur_privilege, CTL_TRAP(t), PC))
  }

/*!
 * Causes the processor to raise a capability exception by writing the given
 * capability exception cause and register number to the xtval register then
 * signalling an exception. The register number refers to a general purpose
 * register, so will be prepended with a zero bit.
 */
val handle_cheri_reg_exception : (CapEx, regidx) -> unit
function handle_cheri_reg_exception(capEx, regnum) =
  let reg6 = 0b0 @ regnum in
  handle_cheri_cap_exception(capEx, reg6)

/*!
 * Is as [handle_cheri_reg_exception] except that the capability register
 * number uses the special value 0x20 indicating the PCC register.
 */
val handle_cheri_pcc_exception : (CapEx) -> unit
function handle_cheri_pcc_exception(capEx) =
  handle_cheri_cap_exception(capEx, 0b100000)

val pcc_access_system_regs : unit -> bool
function pcc_access_system_regs () = PCC.access_system_regs

/* CHERI fetch address checks */

type ext_fetch_addr_error = CapEx

val ext_fetch_check_pc : (xlenbits, xlenbits) -> Ext_FetchAddr_Check(ext_fetch_addr_error)
function ext_fetch_check_pc(start_pc, pc) = {
  if   start_pc == pc
  then {
    /* We need to perform the permission checks only for the first granule. */
    if      not(PCC.tag)
    then {
      if MTCC.tag
      then Ext_FetchAddr_Error(CapEx_TagViolation)
      else {
        /*
         * We're going to infinite loop, installing an untagged MTCC to PCC
         * and coming right back here.  Much better to just stop now.
         *
         * TODO: We'd rather go through the HTIF exit path, but the HTIF
         * registers are not available to us at this point in the code, and
         * changing that would require changes in the upstream submodule.
         * Something to consider when we're rebasing against Zcheripurecap.
         */
        not_implemented ("Untagged PCC and MTCC infinite loops; stopping now")
      }
    }
    else if isCapSealed(PCC)
    then    internal_error(__FILE__, __LINE__, "PCC should never be sealed")
    else if not(PCC.permit_execute)
    then    internal_error(__FILE__, __LINE__, "PCC should always be executable")
    else if not(inCapBounds(PCC, pc, 2))
    then    Ext_FetchAddr_Error(CapEx_BoundsViolation)
    else    Ext_FetchAddr_OK(pc)
  } else {
    /* Perform only the bounds checks on the current granule, i.e. pc. */
    if      not(inCapBounds(PCC, pc, 2))
    then    Ext_FetchAddr_Error(CapEx_BoundsViolation)
    else    Ext_FetchAddr_OK(pc)
  }
}

function ext_handle_fetch_check_error(e : ext_fetch_addr_error) -> unit = {
  if e == CapEx_BoundsViolation then {
    // Always clear the tag on PCC when taking a bounds violation on fetch.
    // This avoids having to do a representability check on MEPCC
    // when the PC goes out of bounds.
    PCC = clearTag(PCC);
  };
  handle_cheri_pcc_exception(e)
}

/* CHERI control address checks */

type ext_control_addr_error = (CapEx, capreg_idx)

/* the control address is derived from a non-PC register, e.g. in JALR */
function ext_control_check_addr(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) = {
  // We used to do bounds check here but this is now performed only on
  // instruction fetch
  Ext_ControlAddr_OK(pc)
}

/* the control address is derived from the PC register, e.g. in JAL */
function ext_control_check_pc(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) = {
  Ext_ControlAddr_OK(pc)
}

function ext_handle_control_check_error(err : ext_control_addr_error) -> unit = {
  internal_error(__FILE__, __LINE__, "ext_handle_control_check_error should be unreachable")
}

/* CHERI data address checks */

type ext_data_addr_error = (CapEx, capreg_idx)

function ext_data_get_addr(base_reg : regidx, offset : xlenbits, acc : AccessType(ext_access_type), width : word_width)
         -> Ext_DataAddr_Check(ext_data_addr_error) = {

  let auth_val = C(base_reg, rs_na);
  let newAddr = auth_val.address + offset;
  let auth_idx = 0b0 @ base_reg;

  let (have_rqd_load_perm, have_rqd_store_perm) : (bool, bool) = match acc {
    Read(Data)            => (auth_val.permit_load, true                 ),
    Write(Data)           => (true                , auth_val.permit_store),
    ReadWrite(Data, Data) => (auth_val.permit_load, auth_val.permit_store),
    Execute()             => internal_error(__FILE__, __LINE__,"ext_data_get_addr for Execute"),
    Read(_)               => internal_error(__FILE__, __LINE__,"ext_data_get_addr for Read(_)"),
    Write(_)              => internal_error(__FILE__, __LINE__,"ext_data_get_addr for Write(_)"),
    ReadWrite(_, _)       => internal_error(__FILE__, __LINE__,"ext_data_get_addr for ReadWrite(_, _)")
  };

  if not(auth_val.tag) then
    Ext_DataAddr_Error(CapEx_TagViolation, auth_idx)
  else if isCapSealed(auth_val) then
    Ext_DataAddr_Error(CapEx_SealViolation, auth_idx)
  else if not(have_rqd_load_perm) then
    Ext_DataAddr_Error(CapEx_PermitLoadViolation, auth_idx)
  else if not(have_rqd_store_perm) then
    Ext_DataAddr_Error(CapEx_PermitStoreViolation, auth_idx)
  else if not(inCapBounds(auth_val, newAddr, word_width_bytes(width))) then
    Ext_DataAddr_Error(CapEx_BoundsViolation, auth_idx)
  else
    Ext_DataAddr_OK(newAddr)
}

function ext_handle_data_check_error(err : ext_data_addr_error) -> unit = {
  let (capEx, regnum) = err;
  handle_cheri_cap_exception(capEx, regnum)
}

/* Default implementations of these hooks permit all accesses.  */
function ext_check_phys_mem_read (access_type, paddr, size, aquire, release, reserved, read_meta) =
  Ext_PhysAddr_OK()

function ext_check_phys_mem_write(write_kind, paddr, size, data, metadata) = {
  if ((paddr >=_u MSHWMB) & (paddr <_u MSHWM)) then {
    /* align down MSHWM to 16 bytes */
    paddr16 = legalize_mshwm(paddr);
    if get_config_print_reg()
    then print_reg("MSHWM <- " ^ BitStr(paddr16));
    MSHWM = paddr16;
  };
  Ext_PhysAddr_OK()
}

/* Is XRET from given mode permitted by extension? */
function ext_check_xret_priv (p : Privilege) : Privilege -> bool =
  pcc_access_system_regs()

/* Called if above check fails */
function ext_fail_xret_priv () : unit -> unit = 
  handle_cheri_pcc_exception(CapEx_AccessSystemRegsViolation)

function ext_check_CSR (csrno : bits(12), p : Privilege, isWrite : bool) -> bool = 
  if not(pcc_access_system_regs()) then match (csrno) {
    /* CSR allow list in absence of access system registers */
    0xB00 => not(isWrite), // mcycle
    0xB02 => not(isWrite), // minstret
    0xB80 => not(isWrite), // mcycleh
    0xB82 => not(isWrite), // minstreth
    0xC00 => not(isWrite), // cycle
    0xC01 => not(isWrite), // time
    0xC02 => not(isWrite), // instret
    0xC80 => not(isWrite), // cycleh
    0xC81 => not(isWrite), // timeh
    0xC82 => not(isWrite), // instreth
    _     => false
  } else {
    true
  }

function ext_check_CSR_fail () -> unit =
  handle_cheri_pcc_exception(CapEx_AccessSystemRegsViolation)
