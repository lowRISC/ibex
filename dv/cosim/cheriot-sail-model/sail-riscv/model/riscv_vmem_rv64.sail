/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* RV64 Supervisor-mode address translation and page-table walks. */

/* Define the architectural satp and its legalizer. */

register satp : xlenbits

function legalize_satp(a : Architecture, o : xlenbits, v : xlenbits) -> xlenbits =
  legalize_satp64(a, o, v)

/* Define valid source addresses for translation */

function isValidSv39Addr(vAddr : xlenbits) -> bool = {
  vAddr[63 .. 39] == (if   vAddr[38] == bitone
                      then ones()
                      else zeros())
}

function isValidSv48Addr(vAddr : xlenbits) -> bool = {
  vAddr[63 .. 48] == (if   vAddr[47] == bitone
                      then ones()
                      else zeros())
}

/* Compute the address translation mode. */

val translationMode : (Privilege) -> SATPMode
function translationMode(priv) = {
  if priv == Machine then Sbare
  else {
    let arch = architecture(get_mstatus_SXL(mstatus));
    match arch {
      Some(RV64) => {
        let mbits : satp_mode = Mk_Satp64(satp)[Mode];
        match satp64Mode_of_bits(RV64, mbits) {
          Some(m) => m,
          None()  => internal_error(__FILE__, __LINE__, "invalid RV64 translation mode in satp")
        }
      },
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

  let asid = curAsid64(satp);
  let ptb  = curPTB64(satp);

  /* PTW extensions: initialize the PTW extension state. */
  let ext_ptw : ext_ptw = init_ext_ptw;

  match mode {
    Sbare => TR_Address(vAddr, ext_ptw),
    Sv39  => { if   isValidSv39Addr(vAddr)
               then match translate39(asid, ptb, vAddr[38 .. 0], ac, effPriv, mxr, do_sum, SV39_LEVELS - 1, ext_ptw) {
                      TR_Address(pa, ext_ptw) => TR_Address(zero_extend(pa), ext_ptw),
                      TR_Failure(f, ext_ptw)  => TR_Failure(translationException(ac, f), ext_ptw)
                    }
               else TR_Failure(translationException(ac, PTW_Invalid_Addr()), ext_ptw)
             },
    Sv48  => { if   isValidSv48Addr(vAddr)
               then match translate48(asid, ptb, vAddr[47 .. 0], ac, effPriv, mxr, do_sum, SV48_LEVELS - 1, ext_ptw) {
                      TR_Address(pa, ext_ptw) => TR_Address(zero_extend(pa), ext_ptw),
                      TR_Failure(f, ext_ptw)  => TR_Failure(translationException(ac, f), ext_ptw)
                    }
               else TR_Failure(translationException(ac, PTW_Invalid_Addr()), ext_ptw)
             },
    _     => internal_error(__FILE__, __LINE__, "unsupported address translation scheme")
  }
}

val translateAddr : (xlenbits, AccessType(ext_access_type)) -> TR_Result(xlenbits, ExceptionType)
function translateAddr(vAddr, ac) =
  translateAddr_priv(vAddr, ac, effectivePrivilege(ac, mstatus, cur_privilege))

val flush_TLB : (option(xlenbits), option(xlenbits)) -> unit
function flush_TLB(asid_xlen, addr_xlen) -> unit = {
  /* Flush both Sv39 and Sv48 TLBs. */
  let (addr39, addr48) : (option(vaddr39), option(vaddr48)) =
    match addr_xlen {
      None()  => (None(), None()),
      Some(a) => (Some(a[38 .. 0]), Some(a[47 .. 0]))
    };
  let asid : option(asid64) =
    match asid_xlen {
      None()  => None(),
      Some(a) => Some(a[15 .. 0])
  };
  flush_TLB39(asid, addr39);
  flush_TLB48(asid, addr48)
}

function init_vmem() -> unit = {
  init_vmem_sv39();
  init_vmem_sv48()
}
