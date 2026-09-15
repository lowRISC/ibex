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

/* Capability versions of mode-dependent instructions */

union clause ast = AUIPCC : (bits(20), regidx)
/*!
 * Capability register *cd* is replaced with the contents of **PCC**, with the
 * **address** replaced with **PCC**.**address** $+$ *imm* $\times$ 2048.
 */
function clause execute AUIPCC(imm, cd) = {
  let off : xlenbits = sign_extend(imm) << 11;
  let (representable, newCap) = setCapAddr(PCC, PC + off);
  C(cd) = clearTagIf(newCap, not(representable));
  RETIRE_SUCCESS
}

union clause ast = AUICGP : (bits(20), regidx)
/*!
 * Capability register *cd* is replaced with the contents of **CGP** (c3), with the
 * **address** replaced with **CGP**.**address** $+$ *imm* $\times$ 2048.
 */
function clause execute AUICGP(imm, cd) = {
  let off : xlenbits = sign_extend(imm) << 11;
  let cgp_val = C(CGP_IDX, rs_na); /* $c3 */
  let (representable, newCap) = incCapAddr(cgp_val, off);
  C(cd) = clearTagIf(newCap, isCapSealed(cgp_val) | not(representable));
  RETIRE_SUCCESS
}

union clause ast = CJAL : (bits(21), regidx)
/*!
 * Capability register *cd* is replaced with the next instruction's **PCC** and
 * sealed as a sentry. **PCC**.**address** is incremented by *imm*.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - **PCC**.**address** $+$ *imm* is unaligned, ignoring bit 0.
 * 
 * ## Notes
 *   - This instruction no longer attempts to check that the destination is
 *     within the bounds of PCC.  In that case an exception will be raised 
 *     raised by the subsequent instruction fetch.  EPCC will have the new
 *     PC as address but will have the tag cleared due to the possibility of 
 *     creating an unrepresentable PCC.  The bounds of EPCC will be 
 *     undefined.
 */
function clause execute(CJAL(imm, cd)) = {
  let off : xlenbits = sign_extend(imm);
  let newPC = PC + off;

  if newPC[1] == bitone & ~(haveRVC()) then {
    handle_mem_exception(newPC,  E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not (isCapSealed(linkCap)), "Link cap should always be unsealed");

    if cd == ra then {
      /* When writing to ra, generate a sealed return capability. */
      let sentry_type = if mstatus.MIE() == 0b1 then otype_sentry_bie else otype_sentry_bid;
      C(cd) = sealCap(linkCap, to_bits(cap_otype_width, sentry_type));
    } else {
      /* Generate an unsealed return capability. */
      C(cd) = linkCap;
    };

    nextPC = newPC;
    RETIRE_SUCCESS
  }
}

union clause ast = CJALR : (bits(12), regidx, regidx)
/*!
 * Capability register *cd* is replaced with the next instruction's **PCC** and
 * sealed as a sentry. **PCC** is replaced with the value of capability
 * register *cs1* with its **address** incremented by *imm* and the 0th bit of
 * its **address** set to 0, and is unsealed if it is a sentry.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed and *imm* $\ne$ 0
 *   - None of the following combinations hold:
 *      1. *cd* = *cnull*, *cs1* = *cra* and *cs1* is a backwards sentry (Function return aka *cret* is only permitted to backwards sentry)
 *      2. *cd* = *cnull*, *cs1* $ne$ *cra* and *cs1* is unsealed or a forwards interrupt inheriting sentry (Tail calls are only permitted to unsealed caps or interrupt handling sentry using a target register different from *cra*, with the return register *cra* set by a different instruction)
 *      3. *cd* $\ne$ *cnull* and *cs1* is unsealed or a forwards interrupt inheriting sentry (Less restricted function calls to interrupt inheriting sentries)
 *      4. *cd* = *cra* and *cs1* is unsealed or a forwards sentry (Function calls are only permitted to unsealed caps or forwards sentry, with link register *cra*)
 *   - *cs1*.**perms** does not grant **Permit_Execute**.
 *   - *cs1*.**address** $+$ *imm* is unaligned, ignoring bit 0.
 *
  * ## Notes
 *   - This instruction no longer attempts to check that the destination is
 *     within the bounds of PCC.  In that case an exception will be raised 
 *     raised by the subsequent instruction fetch.  EPCC will have the new
 *     PC as address but will have the tag cleared due to the possibility of 
 *     creating an unrepresentable PCC.  The bounds of EPCC will be 
 *     undefined.
 */
function clause execute(CJALR(imm, cs1, cd)) = {
  let cs1_val = C(cs1, rs_1);
  let off : xlenbits = sign_extend(imm);
  let newPC = [cs1_val.address + off with 0 = bitzero]; /* clear bit zero as for RISCV JALR */

  let isAllowedSentryType =
    if (cd == zreg & cs1 == ra) then /* this looks like a return */
        isCapBackwardSentry(cs1_val)
    else if (cd == ra) then /* this looks like an ordinary call */
        not(isCapSealed(cs1_val)) | isCapForwardSentry(cs1_val)
    else /* this looks like a tail or outlined call */
        not(isCapSealed(cs1_val)) | isCapForwardInheritSentry(cs1_val);

  if not (cs1_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if (isCapSealed(cs1_val) & imm != zeros()) |
             not (isAllowedSentryType) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not (cs1_val.permit_execute) then {
    handle_cheri_reg_exception(CapEx_PermitExecuteViolation, cs1);
    RETIRE_FAIL
  } else if newPC[1] == bitone & ~(haveRVC()) then {
    handle_mem_exception(newPC,  E_Fetch_Addr_Align());
    RETIRE_FAIL
  } else {
    let (success, linkCap) = setCapAddr(PCC, nextPC); /* Note that nextPC accounts for compressed instructions */
    assert(success, "Link cap should always be representable.");
    assert(not (isCapSealed(linkCap)), "Link cap should always be unsealed");

    if cd == ra then {
      /*
       * When writing to ra, generate a sealed return capability.  We can get
       * here with cs1 unsealed or any forward sentry type.
       */
      let sentry_type = if mstatus.MIE() == 0b1 then otype_sentry_bie else otype_sentry_bid;
      C(cd) = sealCap(linkCap, to_bits(cap_otype_width, sentry_type));
    } else {
      /*
       * Generate an unsealed return capability.  From the conditions above, it
       * must be the case that cs1 is unsealed or a forward inheriting sentry.
       */
      C(cd) = linkCap;
    };

    nextPC = newPC;
    nextPCC = unsealCap(cs1_val);
    if unsigned(cs1_val.otype) == otype_sentry_id | unsigned(cs1_val.otype) == otype_sentry_bid then
      mstatus->MIE() = 0b0;
    if unsigned(cs1_val.otype) == otype_sentry_ie | unsigned(cs1_val.otype) == otype_sentry_bie then
      mstatus->MIE() = 0b1;
    RETIRE_SUCCESS
  }
}

/* Operations that extract parts of a capability into GPR */

union clause ast = CGetPerm   : (regidx, regidx)
union clause ast = CGetType   : (regidx, regidx)
union clause ast = CGetBase   : (regidx, regidx)
union clause ast = CGetLen    : (regidx, regidx)
union clause ast = CGetTag    : (regidx, regidx)
union clause ast = CGetAddr   : (regidx, regidx)
union clause ast = CGetHigh   : (regidx, regidx)
union clause ast = CGetTop    : (regidx, regidx)

/*!
 * The least significant bits of integer register *rd* are
 * set equal to the **perms** field of capability register *cs1*.
 * The other bits of *rd* are set to zero.
 */
function clause execute (CGetPerm(rd, cs1)) = {
  let capVal = C(cs1, rs_1);
  X(rd) = zero_extend(getCapPerms(capVal));
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **otype** field of capability
 * register *cs1*.
 */
function clause execute (CGetType(rd, cs1)) = {
  let capVal = C(cs1, rs_1);
  X(rd) = zero_extend(capVal.otype);
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **base** field of capability
 * register *cs1*.
 */
function clause execute (CGetBase(rd, cs1)) = {
  let capVal = C(cs1, rs_1);
  X(rd) = getCapBaseBits(capVal);
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **high half** of capability
 * register *cs1*.
 *
 * The bits returned here are of the **in-memory** form of the capability, which
 * may differ from microarchitectural forms in use within implementations.
 * That is, applying [CGetHigh] to a capability loaded
 * from address *m* will yield the same result as loading the high half of the
 * capability-sized granule at *m* (that is, bits above **XLEN** when a
 * capability is interpreted as a twice-**XLEN**-bit integer).
 */
function clause execute (CGetHigh(rd, cs1)) = {
  let capVal : Capability = C(cs1, rs_1);
  X(rd) = capToBits(capVal)[sizeof(xlen) * 2 - 1 .. sizeof(xlen)];
  RETIRE_SUCCESS
}

union clause ast = CSetHigh : (regidx, regidx, regidx)
/*!
 * Capability register *cd* comes to hold the capability from *cs1* with its
 * high bits replaced with the value in the integer register *rs2*.  The tag
 * of *cd* is cleared.
 *
 * *rs2* holds the **in-memory** form of capability bits.  That is, this
 * instruction yields the same result as writing *cs1* out to memory,
 * overwriting the high word with *rs2*, and loading that capability-sized
 * granule into *cd*, although without the memory mutation side-effects.
 *
 */
function clause execute (CSetHigh(cd, cs1, rs2)) = {
  let capVal = C(cs1, rs_1);
  let intVal = X(rs2, rs_2);
  let capLow : xlenbits = capToBits(capVal)[sizeof(xlen) - 1 .. 0];
  let newCap : Capability = capBitsToCapability(false, intVal @ capLow);
  C(cd) = newCap;
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **top** field of capability
 * register *cs1*.
 *
 * ## Notes
 *
 * - Due to the compressed representation of capabilities, the actual top
 *   of capabilities can be $2^{[{xlen}][xlen]}$; [CGetTop] will return the
 *   maximum value of $2^{[{xlen}][xlen]}-1$ in this case.
 */
function clause execute (CGetTop(rd, cs1)) = {
  let capVal = C(cs1, rs_1);
  let top = getCapTop(capVal);
  X(rd) = to_bits(sizeof(xlen), if top > cap_max_addr then cap_max_addr else top);
  RETIRE_SUCCESS
}

/*
 * Note: We have to use [{xlen}][xlen] instead of [xlen] to avoid \lstinline{}
 * inside math mode.
 */
/*!
 * Integer register *rd* is set equal to the **length** field of capability
 * register *cs1*.
 *
 * ## Notes
 *
 * - Due to the compressed representation of capabilities, the actual length
 *   of capabilities can be $2^{[{xlen}][xlen]}$; [CGetLen] will return the
 *   maximum value of $2^{[{xlen}][xlen]}-1$ in this case.
 */
function clause execute (CGetLen(rd, cs1)) = {
  let capVal = C(cs1, rs_1);
  let len = getCapLength(capVal);
  X(rd) = to_bits(sizeof(xlen), if len > cap_max_addr then cap_max_addr else len);
  RETIRE_SUCCESS
}

/*!
 * The low bit of integer register *rd* is set to the **tag** field of *cs1*.
 * All other bits of *rd* are cleared.
 */
function clause execute (CGetTag(rd, cs1)) = {
  let capVal = C(cs1, rs_1);
  X(rd) = zero_extend(bool_to_bits(capVal.tag));
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **address** field of capability
 * register *cs1*.
 */
function clause execute (CGetAddr(rd, cs1)) = {
  let capVal = C(cs1, rs_1);
  X(rd) = capVal.address;
  RETIRE_SUCCESS
}

$ifdef RVFI_DII
val rvfi_rSCR : (screg, CapBits, bool) -> unit
function rvfi_rSCR (r,v,t) = {
  rvfi_cheri_scr_data[rvfi_scr_addr]  = zero_extend(r);
  rvfi_cheri_scr_data[rvfi_scr_rdata] = zero_extend(v);
  rvfi_cheri_scr_data[rvfi_scr_rtag] = to_bits(8, if t then 1 else 0);
  rvfi_cheri_scr_data_present = true;
}
$else
val rvfi_rSCR : (screg, CapBits, bool) -> unit
function rvfi_rSCR (r,v,t) = ()
$endif

$ifdef RVFI_DII
val rvfi_wSCR : (screg, CapBits, bool) -> unit
function rvfi_wSCR (r,v,t) = {
  rvfi_cheri_scr_data[rvfi_scr_addr]  = zero_extend(r);
  rvfi_cheri_scr_data[rvfi_scr_wdata] = zero_extend(v);
  rvfi_cheri_scr_data[rvfi_scr_wtag] = to_bits(8, if t then 1 else 0);
  rvfi_cheri_scr_data_present = true;
}
$else
val rvfi_wSCR : (screg, CapBits, bool) -> unit
function rvfi_wSCR (r,v,t) = ()
$endif

union clause ast = CSpecialRW : (regidx, screg, regidx)
/*!
 * Capability register *cd* is set equal to special capability register *scr*,
 * and *scr* is set equal to capability register *cs1* if *cs1* is not **C0**.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *scr* does not exist.
 *   - *scr* requires **Permit_Access_System_Registers** and that is not
 *     granted by **PCC**.**perms**.
 *
 * ## Notes
 *
 * - Writing **NULL** to a special capability register cannot be done with **C0**
 *   as that only performs a read. An alternative implementation would allocate
 *   a separate two-operand CSpecialR instruction and interpret *cs1* being
 *   **C0** as a write of **NULL** if the need to use a temporary capability
 *   register proves to be overly problematic for software.
 * 
 * - MEPCC and MTCC are validated and legalized on write. Any invalid write will
 *   cause the tag to be cleared which might result in a tag violation
 *   on instruction fetch following MRET or exception.
 */
function clause execute (CSpecialRW(cd, scr, cs1)) = {
  let specialExists : bool = match unsigned(scr) {
    28 => true,
    29 => true,
    30 => true,
    31 => true,
    _  => false
  };
  if (not(specialExists)) then {
    handle_illegal();
    RETIRE_FAIL
  } else if not(PCC.access_system_regs) then {
    handle_cheri_cap_exception(CapEx_AccessSystemRegsViolation, 0b1 @ scr);
    RETIRE_FAIL
  } else {
    var cs1_val = C(cs1, rs_1);
    let scr_val : Capability = match unsigned(scr) {
      28 => MTCC,
      29 => MTDC,
      30 => MScratchC,
      31 => MEPCC,
      _  => {assert(false, "unreachable"); undefined}
    };
    C(cd) = scr_val;
    rvfi_rSCR(scr, capToBits(scr_val), scr_val.tag); /* note that cd!=c0 is NOT a requirement for CSpecialRW reads */
    if (cs1 != zeros()) then {
      rvfi_wSCR(scr, capToBits(cs1_val), cs1_val.tag); /* may be overridden below; cs1!=c0 check already done */
      match unsigned(scr) {
        28 => {
          /* Validate that the new MTCC is unsealed, executable and 
             indicates direct trap mode */
          let invalid = cs1_val.address[1..0] != 0b00 |
            isCapSealed(cs1_val) |
            not(cs1_val.permit_execute);
          /* Legalize MTCC.address / mtvec */
          cs1_val.address[1..0] = 0b00;
          cs1_val = clearTagIf(cs1_val, invalid);
          rvfi_wSCR(scr, capToBits(cs1_val), cs1_val.tag); /* override prior value and tag */
          MTCC = cs1_val
        },
        29 => MTDC = cs1_val,
        30 => MScratchC = cs1_val,
        31 => {
          /* Validate that new MEPCC is aligned, unsealed and executable */
          let invalid = cs1_val.address[0] != bitzero |
            isCapSealed(cs1_val) |
            not(cs1_val.permit_execute);
          /* Legalize MEPCC.address / mepc */
          cs1_val.address[0] = bitzero;
          cs1_val = clearTagIf(cs1_val, invalid);
          rvfi_wSCR(scr, capToBits(cs1_val), cs1_val.tag); /* override prior value and tag */
          MEPCC = cs1_val
        },
        _  => assert(false, "unreachable")
      }
    };
    RETIRE_SUCCESS
  }
}

union clause ast = CAndPerm : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of capability
 * register *cs1* with the **perms** field set to the bitwise AND of its
 * previous value and bits 0 to [cap_perms_width]-1 of integer register *rs2*.
 * If the resulting set of permissions cannot be represented by the capability
 * encoding then the result will have a (possibly empty) subset of the ANDed
 * permissions. If *cs1* was sealed and *rs2* codes for clearing anything other
 * than Permit_Global, then *cd*.**tag** is cleared.
 */
function clause execute(CAndPerm(cd, cs1, rs2)) = {
  let cs1_val = C(cs1, rs_1);
  let rs2_val = X(rs2, rs_2);

  let perms = getCapPerms(cs1_val);
  let mask = truncate(rs2_val, cap_perms_width);

  let newperms = perms & mask;

  /*
   * CAndPerm on a sealed cap clears the tag unless the mask is all ones or
   * has *only* the global permission clear.
   *
   * Here, perm_global is a bit vector (in the architectural format used by
   * [CAndPerm] and [CGetPerm]) of all zeros except for the global permission
   * bit.  Its formulation here relies on null_cap having no asserted
   * permissions (which we verify in our SMT properties; see
   * [prop_null_noperms]).
   */
  let perm_global = getCapPerms({ null_cap with global = true });
  let inCap = clearTagIf(cs1_val,
                isCapSealed(cs1_val) & ((mask | perm_global) != ones()));

  let newCap = setCapPerms(inCap, newperms);

  C(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = CSub : (regidx, regidx, regidx)
/*!
 * Integer register *rd* is set equal to (*cs1*.**address** $-$
 * *cs2*.**address**) $\bmod~2^{[{xlen}][xlen]}$.
 */
function clause execute(CSub(rd, cs1, cs2)) = {
  let cs2_val = C(cs2, rs_2);
  let cs1_val = C(cs1, rs_1);

  X(rd) = cs1_val.address - cs2_val.address;
  RETIRE_SUCCESS
}

union clause ast = CIncAddr : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *cs1*.**address** $+$ *rs2*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *cs1*.**address** $+$ *rs2* decodes to.
 */
function clause execute (CIncAddr(cd, cs1, rs2)) = {
  let cs1_val = C(cs1, rs_1);
  let rs2_val = X(rs2, rs_2);

  let inCap = clearTagIfSealed(cs1_val);
  let (success, newCap) = incCapAddr(inCap, rs2_val);

  C(cd) = clearTagIf(newCap, not(success));
  RETIRE_SUCCESS
}

union clause ast = CIncAddrImmediate : (regidx, regidx, bits(12))
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *cs1*.**address** $+$ *imm*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *cs1*.**address** $+$ *imm* decodes to.
 */
function clause execute (CIncAddrImmediate(cd, cs1, imm)) = {
  let cs1_val = C(cs1, rs_1);
  let immBits : xlenbits = sign_extend(imm);

  let inCap = clearTagIfSealed(cs1_val);
  let (success, newCap) = incCapAddr(inCap, immBits);

  C(cd) = clearTagIf(newCap, not(success));
  RETIRE_SUCCESS
}

union clause ast = CSetAddr : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *rs2*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *rs2* decodes to.
 */
function clause execute (CSetAddr(cd, cs1, rs2)) = {
  let cs1_val = C(cs1, rs_1);
  let rs2_val = X(rs2, rs_2);

  let inCap = clearTagIfSealed(cs1_val);
  let (representable, newCap) = setCapAddr(inCap, rs2_val);

  C(cd) = clearTagIf(newCap, not(representable));
  RETIRE_SUCCESS
}


union clause ast = CSetBounds : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set to capability register *cs1* with its
 * **base** field replaced with *cs1*.**address** and its **length** field
 * replaced with integer register *rs2*. If the resulting capability cannot be
 * represented exactly the **base** will be rounded down and the **length**
 * will be rounded up by the smallest amount needed to form a representable
 * capability covering the requested bounds. The **tag** field of the result
 * is cleared if the bounds of the result exceed the bounds of *cs1*, or if
 * *cs1* was sealed.
 *
 * ## Notes
 *
 *  - This Sail code actually does the bounds check on the *requested* bounds,
 *    not the bounds that result from [setCapBounds]. This is an important
 *    distinction because the resulting bounds may be larger than the requested
 *    bounds, which could potentially lead to non-monotonic behaviour.
 *    However, providing that [setCapBounds] always returns the most precise
 *    encodable bounds it is safe to do the check on the requested bounds because,
 *    in the worst case, it would return the existing bounds. This is desirable
 *    because in hardware the bounds checking can be performed in parallel with
 *    computing the new bounds.
 */
function clause execute (CSetBounds(cd, cs1, rs2)) = {
  let cs1_val = C(cs1, rs_1);
  let rs2_val = X(rs2, rs_2);

  let newBase = cs1_val.address;
  let newLen  = rs2_val;
  let inBounds = inCapBounds(cs1_val, newBase, unsigned(newLen));

  let inCap = clearTagIfSealed(cs1_val);
  let (_, newCap) = setCapBounds(inCap, newBase, newLen);

  C(cd) = clearTagIf(newCap, not(inBounds)); /* ignore exact */
  RETIRE_SUCCESS
}

union clause ast = CSetBoundsImmediate : (regidx, regidx, bits(12))
/*!
 * Capability register *cd* is set to capability register *cs1* with its
 * **base** field replaced with *cs1*.**address** and its **length** field
 * replaced with *uimm*. If the resulting capability cannot be represented
 * exactly the **base** will be rounded down and the **length** will be rounded
 * up by the smallest amount needed to form a representable capability covering
 * the requested bounds. The **tag** field of the result is cleared if the
 * bounds of the result exceed the bounds of *cs1*, or if *cs1* was sealed.
 *
 * ## Notes
 *  - The same caveat regarding the order of the bounds check applies as for
 *    [CSetBounds].
 */
function clause execute (CSetBoundsImmediate(cd, cs1, uimm)) = {
  let cs1_val = C(cs1, rs_1);

  let newBase = cs1_val.address;
  let newLen : CapAddrBits = zero_extend(uimm);
  let inBounds = inCapBounds(cs1_val, newBase, unsigned(newLen));

  let inCap = clearTagIfSealed(cs1_val);
  let (_, newCap) = setCapBounds(inCap, newBase, newLen);

  C(cd) = clearTagIf(newCap, not(inBounds)); /* ignore exact */
  RETIRE_SUCCESS
}

union clause ast = CSetBoundsExact : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set to capability register *cs1* with its
 * **base** field replaced with *cs1*.**address** and its **length** field
 * replaced with integer register *rs2*. If the resulting capability cannot be
 * represented exactly, the **tag** field will be cleared (unlike [CSetBounds]),
 * the **base** will be rounded down and the **length** will be rounded up by
 * the smallest amount needed to form a representable capability covering the
 * requested bounds. The **tag** field of the result is cleared if the bounds
 * of the result exceed the bounds of *cs1*, or if *cs1* was sealed.
 *
 * ## Notes
 *  - The same caveat regarding the order of the bounds check applies as for
 *    [CSetBounds].
 */
function clause execute (CSetBoundsExact(cd, cs1, rs2)) = {
  let cs1_val = C(cs1, rs_1);
  let rs2_val = X(rs2, rs_2);

  let newBase = cs1_val.address;
  let newLen = X(rs2, rs_2);
  let inBounds = inCapBounds(cs1_val, newBase, unsigned(newLen));

  let inCap = clearTagIfSealed(cs1_val);
  let (exact, newCap) = setCapBounds(inCap, newBase, newLen);

  C(cd) = clearTagIf(newCap, not(inBounds & exact));
  RETIRE_SUCCESS
}

union clause ast = CSetBoundsRoundDown : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set to the capability in register *cs1* with its
 * **base** field replaced with *cs1*.**address** and its **length** field
 * replaced with a representable value no larger than the value in the integer
 * register *rs2*.  That **length** will be nonzero if *rs2* is nonzero.
 *
 * ## Notes
 *
 *  - As with [CSetBounds], the implementation here does the bounds check on the
 *    *requested* bounds.  This is less interesting here than there because the
 *    results of [setCapBoundsRoundDown] are always a subset of the requested
 *    range.
 *
 *  - The present implementation returns the largest representable span from the
 *    given base (*cs1*.**address**) whose length is no more than *rs2*, except
 *    that it will not return anything larger than the largest capability
 *    representable with an exponent of 14.  This caveat simplifies handling of
 *    very large capabilities, which we do not expect to be used with this
 *    instruction in practice.  However, we may revisit this decision in future
 *    editions; software should depend only on the result being representable
 *    and of non-zero length (unless *rs2* was zero).
 */
function clause execute (CSetBoundsRoundDown(cd, cs1, rs2)) = {
  let cs1_val = C(cs1, rs_1);
  let rs2_val = X(rs2, rs_2);

  let newBase = cs1_val.address;
  let newLen = rs2_val;
  let inBounds = inCapBounds(cs1_val, newBase, unsigned(newLen));
  let inCap = clearTagIfSealed(cs1_val);
  let newCap = setCapBoundsRoundDown(inCap, newBase, newLen);
  C(cd) = clearTagIf(newCap, not(inBounds));
  RETIRE_SUCCESS
}

union clause ast = CClearTag : (regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of *cs1*, with
 * the **tag** field cleared.
 */
function clause execute (CClearTag(cd, cs1)) = {
  let cs1_val = C(cs1, rs_1);
  C(cd) = clearTag(cs1_val);
  RETIRE_SUCCESS
}

union clause ast = CMove : (regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of *cs1*.
 */
function clause execute (CMove(cd, cs1)) = {
  C(cd) = C(cs1, rs_1);
  RETIRE_SUCCESS
}

union clause ast = CRRL : (regidx, regidx)
/*!
 * Integer register *rd* is set to the smallest value greater or equal to *rs1*
 * that can be used as a length to set exact bounds on a capability that has a
 * suitably aligned base (as obtained with the help of [CRAM]). Note that this
 * could round up the length to $2^{[{xlen}][xlen]}$ in which case *rd* will be 
 * set to zero. Users should be careful to account for this case.
 */
function clause execute(CRRL(rd, rs1)) = {
  let len = X(rs1, rs_1);
  X(rd) = getRepresentableLength(len);
  RETIRE_SUCCESS
}

union clause ast = CRAM : (regidx, regidx)
/*!
 * Integer register *rd* is set to a mask that can be used to round addresses
 * down to to a value that is sufficiently aligned to set exact bounds for the
 * nearest representable length of *rs1* (as obtained by [CRRL]).
 */
function clause execute(CRAM(rd, rs1)) = {
  let len = X(rs1, rs_1);
  X(rd) = getRepresentableAlignmentMask(len);
  RETIRE_SUCCESS
}

union clause ast = CTestSubset : (regidx, regidx, regidx)
/*!
 * Integer register *rd* is set to 1 if the **tag** fields of capability
 * registers *cs1* and *cs2* are the same and the bounds and permissions of
 * *cs2* are a subset of those of *cs1*.
 *
 * ## Notes
 *
 * - The operand order for this instruction is reversed compared with the
 *   normal RISC-V comparison instructions, but this may be changed in future.
 *
 * - The **otype** field is ignored for this instruction, but an alternative
 *   implementation might wish to consider capabilities with distinct
 *   **otype**s as unordered as is done for the **tag** field.
 */
function clause execute (CTestSubset(rd, cs1, cs2)) = {
  let cs1_val = C(cs1, rs_1);
  let cs2_val = C(cs2, rs_2);

  let (cs2_base, cs2_top) = getCapBounds(cs2_val);
  let (cs1_base, cs1_top) = getCapBounds(cs1_val);
  let cs2_perms = getCapPerms(cs2_val);
  let cs1_perms = getCapPerms(cs1_val);

  let result = if cs1_val.tag != cs2_val.tag then
                 0b0
               else if cs2_base < cs1_base then
                 0b0
               else if cs2_top > cs1_top then
                 0b0
               else if (cs2_perms & cs1_perms) != cs2_perms then
                 0b0
               else
                 0b1;

  X(rd) = zero_extend(result);
  RETIRE_SUCCESS
}

union clause ast = CSEQX : (regidx, regidx, regidx)
/*!
 * Integer register *rd* is set to 1 if the **tag** fields and in-memory
 * representations of capability registers *cs1* and *cs2* are identical,
 * including any reserved encoding bits, otherwise it is set to 0.
 */
function clause execute (CSEQX(rd, cs1, cs2)) = {
  let cs1_val = C(cs1, rs_1);
  let cs2_val = C(cs2, rs_2);
  X(rd) = zero_extend(bool_to_bits(cs1_val == cs2_val));
  RETIRE_SUCCESS
}

union clause ast = CSeal : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with capability register *cs1*, and is
 * sealed with **otype** equal to the **address** field of capability register
 * *cs2*. If *cs2* is unable to authorize the sealing, or if *cs1* was already
 * sealed, then the **tag** field of *cd* is cleared.
 */
function clause execute (CSeal(cd, cs1, cs2)) = {
  let cs1_val = C(cs1, rs_1);
  let cs2_val = C(cs2, rs_2);

  let cs2_addr = unsigned(cs2_val.address);
  let (cs2_base, cs2_top) = getCapBounds(cs2_val);

  let isPermittedOtype : bool =
    if cs1_val.permit_execute then
      match (cs2_addr) {
        /* 0 is unsealed */
        1 => true, /* otype_sentry */
        2 => true, /* otype_sentry_id */
        3 => true, /* otype_sentry_ie */
        4 => true, /* otype_sentry_bid */
        5 => true, /* otype_sentry_bie */
        6 => true,
        7 => true,
        _ => false
      }
    else
      (8 < cs2_addr) & (cs2_addr <= 15);

  let permitted = cs2_val.tag
                & not(isCapSealed(cs2_val))
                & cs2_val.permit_seal
                & (cs2_addr >= cs2_base)
                & (cs2_addr < cs2_top)
                & isPermittedOtype;

  let inCap = clearTagIfSealed(cs1_val);
  let newCap = sealCap(inCap, to_bits(cap_otype_width, cs2_addr));

  C(cd) = clearTagIf(newCap, not(permitted));
  RETIRE_SUCCESS
}

union clause ast = CUnseal : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with capability register *cs1* and is
 * unsealed, using capability register *cs2* as the authority for the unsealing
 * operation. If *cs2*.**perms** does not grant **Global** then *cd*.**perms**
 * is stripped of **Global**. If *cs2* is unable to authorize the unsealing
 * (because *cs1*.**otype** is not within the bounsd of *cs2*),
 * the **tag** field of *cd* is cleared.
 */
function clause execute (CUnseal(cd, cs1, cs2)) = {
  let cs1_val = C(cs1, rs_1);
  let cs2_val = C(cs2, rs_2);
  let cs2_addr = unsigned(cs2_val.address);
  let permitted = cs2_val.tag
                & isCapSealed(cs1_val)
                & not(isCapSealed(cs2_val))
                & inCapBounds(cs2_val, zero_extend(cs1_val.otype), 1)
                & cs2_val.permit_unseal;
  let new_global = cs1_val.global & cs2_val.global;
  let newCap = {unsealCap(cs1_val) with global=new_global};
  C(cd) = clearTagIf(newCap, not(permitted));
  RETIRE_SUCCESS
}

union clause ast = LoadCapImm : (regidx, regidx, bits(12))
/*!
 * Capability register *cd* is
 * replaced with the capability located in memory at *cs1*.**address** $+$
 * *imm*, and if *cs1*.**perms** does not grant **Permit_Load_Capability** then
 * *cd*.**tag** is cleared.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Load**.
 *   - *cs1*.**address** $+$ *imm* $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ *imm* $+$ **CLEN** $/$ 8 $\gt$ *cs1*.**top**.
 *   - *cs1*.**address** $+$ *imm* is unaligned, regardless of whether the
 *     implementation supports unaligned data accesses.
 */
function clause execute LoadCapImm(cd, cs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let auth_val = C(cs1, rs_1);
  let vaddrBits = auth_val.address + offset;
  if not(auth_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not (auth_val.permit_load) then {
    handle_cheri_reg_exception(CapEx_PermitLoadViolation, cs1);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, cap_size)) then {
    handle_cheri_reg_exception(CapEx_BoundsViolation, cs1);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddrBits, cap_size)) then {
    handle_mem_exception(vaddrBits, E_Load_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Read(Cap)) {
    TR_Failure(E_Extension(_), _) => { internal_error(__FILE__, __LINE__,"unexpected cheri exception for cap load") },
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, ptw_info) => {
      let c = mem_read_cap(addr, false, false, false);
      match c {
        MemValue(v) => {
          var cr = v;
          if ptw_info.ptw_lc == PTW_LC_CLEAR  | not(auth_val.permit_load_store_cap) then {
            cr.tag = false;
          };
          if cr.tag & not(auth_val.permit_load_global) then {
            /* Without load-global authority, the loaded cap is always local */
            cr.global = false;
            if not(isCapSealed(cr)) then {
              /*
               * Loading an unsealed capability without load global authority
               * results in attenuation of the loaded capability's permission,
               * transitively weakening the view through said authority.
               *
               * But sealing stops this transitivity.  Even if the authority
               * lacks load global permission, a loaded sealed cap retains its
               * load global permission, as it requires separate unsealing
               * authority to exercise.
               */
              cr.permit_load_global = false;
            }
          };
          if cr.tag & not(auth_val.permit_load_mutable) & not(isCapSealed(cr)) then {
            /*
             * Loading an unsealed capability without load mutable authority
             * also results in attenuated permissions.  As above, sealing stops
             * transitivity, but also the loaded sealed capability retains its
             * store permission.
             */
            cr.permit_store = false;
            cr.permit_load_mutable = false;
          };
          /* Sealing capabilities are excluded from revocation */
          let isSealingCap = cr.permit_seal | cr.permit_unseal | cr.perm_user0;
          if (cr.tag & not(isSealingCap)) then {
            let base = getCapBaseBits(cr);
            let granule_addr = align_down(log2_revocation_granule_size, base);
            let revoked = mem_read_cap_revoked(granule_addr);
            cr.tag = cr.tag & not(revoked);
          };
          C(cd) = cr;
          RETIRE_SUCCESS
        },
        MemException(e) => {handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
      }
    }
  }
}

union clause ast = StoreCapImm : (regidx, regidx, bits(12))
/*!
 * The capability located in memory at *cs1*.**address** $+$ *imm* is
 * replaced with capability register *cs2*.
 *
 * The stored capability will have its tag forcibly cleared if *cs1*.**perms**
 * does not grant **Permit_Store_Local_Capability** and *cs2*.**perms** does not
 * grant **Global**.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Store**.
 *   - *cs1*.**perms** does not grant **Permit_Store_Capability** and
 *     *cs2*.**tag** is set.
 *   - *cs1*.**address** $+$ *imm* $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ *imm* $+$ **CLEN** $/$ 8 $\gt$ *cs1*.**top**.
 */
function clause execute StoreCapImm(cs2, cs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let auth_val = C(cs1, rs_1);
  let vaddrBits = auth_val.address + offset;
  let cs2_val = C(cs2, rs_2);
  if not(auth_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not (auth_val.permit_store) then {
    handle_cheri_reg_exception(CapEx_PermitStoreViolation, cs1);
    RETIRE_FAIL
  } else if not (auth_val.permit_load_store_cap) & cs2_val.tag then {
    handle_cheri_reg_exception(CapEx_PermitStoreCapViolation, cs1);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, cap_size)) then {
    handle_cheri_reg_exception(CapEx_BoundsViolation, cs1);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddrBits, cap_size)) then {
    handle_mem_exception(vaddrBits, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Write(if cs2_val.tag then Cap else Data)) {
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, _) => {
      let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, false, false, false);
      match (eares) {
        MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
        MemValue(_) => {
          let stored_val =
              clearTagIf(cs2_val, not (auth_val.permit_store_local_cap) & not (cs2_val.global));
          let res : MemoryOpResult(bool) = mem_write_cap(addr, stored_val, false, false, false);
          match (res) {
            MemValue(true)  => RETIRE_SUCCESS,
            MemValue(false) => internal_error(__FILE__, __LINE__,"store got false from mem_write_value"),
            MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
          }
        }
      }
    }
  }
}

/* AUICGP is a U-TYPE instruction with its own major opcode.
   AUIPCC reuses the AUIPC encoding: this handled by the post decode hook. */

mapping clause encdec   = AUICGP(imm, cd) if (haveXcheri()) <-> imm : bits(20) @ cd @ 0b1111011 if (haveXcheri())

mapping clause assembly = AUICGP(imm, cd) <-> "auicgp" ^ spc() ^ reg_name(cd) ^ sep() ^ hex_bits_20(imm)
mapping clause assembly = AUIPCC(imm, cd) <-> "auipcc" ^ spc() ^ reg_name(cd) ^ sep() ^ hex_bits_20(imm)

/*
NB: Must be careful about order of matching because unused register
fields are re-used as additional function codes: more specific matches
must come before more general ones. In our case that means two-arg
instructions (that have 0x7f in func7 field) must come before
three-arg ones.
*/

/* Two arg */

mapping clause encdec = CGetPerm(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b00000 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetType(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b00001 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetBase(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b00010 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetLen(rd, cs1)    if (haveXcheri()) <-> 0b1111111 @ 0b00011 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetTag(rd, cs1)    if (haveXcheri()) <-> 0b1111111 @ 0b00100 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetAddr(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b01111 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetHigh(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b10111 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CGetTop(rd, cs1)    if (haveXcheri()) <-> 0b1111111 @ 0b11000 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CMove(cd, cs1)      if (haveXcheri()) <-> 0b1111111 @ 0b01010 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CClearTag(cd, cs1)  if (haveXcheri()) <-> 0b1111111 @ 0b01011 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CRRL(rd, rs1) if (haveXcheri()) <-> 0b1111111 @ 0b01000 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CRAM(rd, rs1) if (haveXcheri()) <-> 0b1111111 @ 0b01001 @ rs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause assembly = CGetPerm(rd, cs1)   <-> "cgetperm"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetType(rd, cs1)   <-> "cgettype"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetBase(rd, cs1)   <-> "cgetbase"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetLen(rd, cs1)    <-> "cgetlen"    ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetTag(rd, cs1)    <-> "cgettag"    ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetAddr(rd, cs1)   <-> "cgetaddr"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetHigh(rd, cs1)   <-> "cgethigh"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetTop(rd, cs1)    <-> "cgettop"    ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = CMove(cd, cs1)         <-> "cmove"      ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CClearTag(cd, cs1)     <-> "ccleartag"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = CRRL(rd, rs1) <-> "crrl" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)
mapping clause assembly = CRAM(rd, rs1) <-> "cram" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1)

/* Three arg */

mapping clause encdec = CSeal(cd, cs1, cs2)       if (haveXcheri()) <-> 0b0001011 @ cs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CUnseal(cd, cs1, cs2)     if (haveXcheri()) <-> 0b0001100 @ cs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CAndPerm(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0001101 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetAddr(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0010000 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetHigh(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0010110 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CIncAddr(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0010001 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBounds(cd, cs1, rs2)  if (haveXcheri()) <-> 0b0001000 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBoundsExact(cd, cs1, rs2) if (haveXcheri()) <-> 0b0001001 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBoundsRoundDown(cd, cs1, rs2) if (haveXcheri()) <-> 0b0001010 @ rs2 @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CSub(rd, cs1, cs2)        if (haveXcheri()) <-> 0b0010100 @ cs2 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CTestSubset(rd, cs1, cs2) if (haveXcheri()) <-> 0b0100000 @ cs2 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSpecialRW(cd, scr, cs1)  if (haveXcheri()) <-> 0b0000001 @ scr @ cs1 @ 0b000 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CIncAddrImmediate(cd, cs1, imm12) if (haveXcheri()) <-> imm12 : bits(12) @ cs1 @ 0b001 @ cd @ 0b1011011 if (haveXcheri())
mapping clause encdec = CSetBoundsImmediate(cd, cs1, imm12) if (haveXcheri()) <-> imm12 : bits(12) @ cs1 @ 0b010 @ cd @ 0b1011011 if (haveXcheri())

mapping clause encdec = CSEQX(rd, cs1, cs2) if (haveXcheri()) <-> 0b0100001 @ cs2 @ cs1 @ 0b000 @ rd @ 0b1011011 if (haveXcheri())

mapping clause assembly = CSeal(cd, cs1, cs2)      <-> "cseal"      ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)
mapping clause assembly = CUnseal(cd, cs1, cs2)    <-> "cunseal"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)
mapping clause assembly = CAndPerm(cd, cs1, rs2)   <-> "candperm"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetAddr(cd, cs1, rs2)   <-> "csetaddr"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetHigh(cd, cs1, rs2)  <-> "csethigh"    ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CIncAddr(cd, cs1, rs2)   <-> "cincaddr" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetBounds(cd, cs1, rs2) <-> "csetbounds" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetBoundsExact(cd, cs1, rs2) <-> "csetboundsexact" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetBoundsRoundDown(cd, cs1, rs2) <-> "csetboundsrounddown" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = CSub(rd, cs1, cs2)      <-> "csub"        ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

mapping clause assembly = CTestSubset(rd, cs1, cs2) <-> "ctestsubset" ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

mapping clause assembly = CSpecialRW(cd, scr, cs1) <-> "cspecialrw"  ^ spc() ^ cap_reg_name(cd) ^ sep() ^ scr_name_map(scr) ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = CIncAddrImmediate(cd, cs1, imm12)   <-> "cincaddrimm" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm12)
mapping clause assembly = CSetBoundsImmediate(cd, cs1, imm12) <-> "csetboundsimm" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm12)

mapping clause assembly = CSEQX(rd, cs1, cs2) <-> "cseqx" ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

/* Loads and stores */

mapping clause encdec = LoadCapImm(cd, rs1, offset) <-> offset @ rs1 @ 0b011 @ cd @ 0b0000011 /* lc */
mapping clause encdec = StoreCapImm(cs2, rs1, off7 @ off5) <-> off7 : bits(7) @ cs2 @ rs1 @ 0b011 @ off5 : bits(5) @ 0b0100011 /* sc */

mapping clause assembly = LoadCapImm(cd, rs1, offset)   <-> "lc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCapImm(cs2, rs1, offset) <-> "sc" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"

/*
 * Encoding/assembly mappings for instructions that overlap existing RISC-V
 * encodings. This does not include loads/stores since they are not decoded
 * differently, but instead use hooks for semantic differences. CHERIoT
 * only supports cap mode so these always have priority over the RISC-V
 * ones.
 */
mapping clause encdec_capmode = AUIPCC(imm, cd) <-> imm @ cd @ 0b0010111
mapping clause assembly = AUIPCC(imm, cd)
  <-> "auipcc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_20(imm)
mapping clause encdec_capmode = CJALR(imm, cs1, cd) <-> imm @ cs1 @ 0b000 @ cd @ 0b1100111
mapping clause assembly = CJALR(imm, cs1, cd)
  <-> "cjalr" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm)
/* See `mapping clause encdec = RISCV_JAL` for why we have to use this syntax */
mapping clause encdec_capmode = CJAL(imm_19 @ imm_7_0 @ imm_8 @ imm_18_13 @ imm_12_9 @ 0b0, cd)
  <-> imm_19 : bits(1) @ imm_18_13 : bits(6) @ imm_12_9 : bits(4) @ imm_8 : bits(1) @ imm_7_0 : bits(8) @ cd @ 0b1101111
mapping clause assembly = CJAL(imm, cd)
  <-> "cjal" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_21(imm)
