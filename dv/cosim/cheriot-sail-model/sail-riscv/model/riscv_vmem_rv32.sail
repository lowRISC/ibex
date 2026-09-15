/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* RV32 Supervisor-mode address translation and page-table walks. */

/* Define the architectural satp and its legalizer. */

register satp : xlenbits

function legalize_satp(a : Architecture, o : xlenbits, v : xlenbits) -> xlenbits =
  legalize_satp32(a, o, v)

/* Compute the address translation mode. */

val translationMode : (Privilege) -> SATPMode
function translationMode(priv) = {
  if priv == Machine then Sbare
  else {
    let arch = architecture(get_mstatus_SXL(mstatus));
    match arch {
      Some(RV32) => {
        let s = Mk_Satp32(satp[31..0]);
        if s[Mode] == 0b0 then Sbare else Sv32
      },
      _    => internal_error(__FILE__, __LINE__, "unsupported address translation arch")
    }
  }
}

/* Top-level address translation dispatcher */

val translateAddr_priv : (xlenbits, AccessType(ext_access_type), Privilege) -> TR_Result(xlenbits, ExceptionType)
function translateAddr_priv(vAddr, ac, effPriv) = {
  let mxr    : bool   = mstatus[MXR] == 0b1;
  let do_sum : bool   = mstatus[SUM] == 0b1;
  let mode : SATPMode = translationMode(effPriv);

  let asid = curAsid32(satp);
  let ptb  = curPTB32(satp);

  /* PTW extensions: initialize the PTW extension state */
  let ext_ptw : ext_ptw = init_ext_ptw;

  match mode {
    Sbare => TR_Address(vAddr, ext_ptw),
    Sv32  => match translate32(asid, ptb, vAddr, ac, effPriv, mxr, do_sum, SV32_LEVELS - 1, ext_ptw) {
               TR_Address(pa, ext_ptw) => TR_Address(to_phys_addr(pa), ext_ptw),
               TR_Failure(f, ext_ptw)  => TR_Failure(translationException(ac, f), ext_ptw)
             },
    _     => internal_error(__FILE__, __LINE__, "unsupported address translation scheme")
  }
}

val translateAddr : (xlenbits, AccessType(ext_access_type)) -> TR_Result(xlenbits, ExceptionType)
function translateAddr(vAddr, ac) =
  translateAddr_priv(vAddr, ac, effectivePrivilege(ac, mstatus, cur_privilege))

val flush_TLB : (option(xlenbits), option(xlenbits)) -> unit
function flush_TLB(asid_xlen, addr_xlen) -> unit = {
  let asid : option(asid32) =
    match (asid_xlen) {
      None()  => None(),
      Some(a) => Some(a[8  .. 0])
    };
  flush_TLB32(asid, addr_xlen)
}

function init_vmem () -> unit = {
  init_vmem_sv32()
}
