/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* address ranges */

// TODO: handle the 34-bit paddr32 on RV32

/* [min, max) of the matching range. */
type pmp_addr_range = option((xlenbits, xlenbits))

function pmpAddrRange(cfg: Pmpcfg_ent, pmpaddr: xlenbits, prev_pmpaddr: xlenbits) -> pmp_addr_range = {
  match pmpAddrMatchType_of_bits(cfg[A]) {
    OFF   => None(),
    TOR   => { Some ((prev_pmpaddr << 2, pmpaddr << 2)) },
    NA4   => {
               // NA4 is not selectable when the PMP grain G >= 1. See pmpWriteCfg().
               assert(sys_pmp_grain() < 1, "NA4 cannot be selected when PMP grain G >= 1.");
               let lo = pmpaddr << 2;
               Some((lo, lo + 4))
             },
    NAPOT => {
               // Example pmpaddr: 0b00010101111
               //                          ^--- last 0 dictates region size & alignment
               let mask = pmpaddr ^ (pmpaddr + 1);
               // pmpaddr + 1:     0b00010110000
               // mask:            0b00000011111
               // ~mask:           0b11111100000
               let lo   = pmpaddr & (~ (mask));
               // mask + 1:        0b00000100000
               let len  = mask + 1;
               Some((lo << 2, (lo + len) << 2))
             }
  }
}

/* permission checks */

val pmpCheckRWX: (Pmpcfg_ent, AccessType(ext_access_type)) -> bool
function pmpCheckRWX(ent, acc) = {
  match acc {
    Read(_)      => ent[R] == 0b1,
    Write(_)     => ent[W] == 0b1,
    ReadWrite(_) => ent[R] == 0b1 & ent[W] == 0b1,
    Execute()    => ent[X] == 0b1
  }
}

// this needs to be called with the effective current privilege.
val pmpCheckPerms: (Pmpcfg_ent, AccessType(ext_access_type), Privilege) -> bool
function pmpCheckPerms(ent, acc, priv) = {
  match priv {
    Machine => if   pmpLocked(ent)
               then pmpCheckRWX(ent, acc)
               else true,
    _       => pmpCheckRWX(ent, acc)
  }
}

/* matching logic */

enum pmpAddrMatch = {PMP_NoMatch, PMP_PartialMatch, PMP_Match}

function pmpMatchAddr(addr: xlenbits, width: xlenbits, rng: pmp_addr_range) -> pmpAddrMatch = {
  match rng {
    None()         => PMP_NoMatch,
    Some((lo, hi)) => if   hi <=_u lo   /* to handle mis-configuration */
                      then PMP_NoMatch
                      else {
                        if      (addr + width <=_u lo) | (hi <=_u addr)
                        then    PMP_NoMatch
                        else if (lo <=_u addr) & (addr + width <=_u hi)
                        then    PMP_Match
                        else    PMP_PartialMatch
                      }
  }
}

enum pmpMatch = {PMP_Success, PMP_Continue, PMP_Fail}

function pmpMatchEntry(addr: xlenbits, width: xlenbits, acc: AccessType(ext_access_type), priv: Privilege,
                       ent: Pmpcfg_ent, pmpaddr: xlenbits, prev_pmpaddr: xlenbits) -> pmpMatch = {
  let rng = pmpAddrRange(ent, pmpaddr, prev_pmpaddr);
  match pmpMatchAddr(addr, width, rng) {
    PMP_NoMatch      => PMP_Continue,
    PMP_PartialMatch => PMP_Fail,
    PMP_Match        => if   pmpCheckPerms(ent, acc, priv)
                        then PMP_Success
                        else PMP_Fail
  }
}

/* priority checks */

function accessToFault(acc : AccessType(ext_access_type)) -> ExceptionType =
  match acc {
    Read(_)      => E_Load_Access_Fault(),
    Write(_)     => E_SAMO_Access_Fault(),
    ReadWrite(_) => E_SAMO_Access_Fault(),
    Execute()    => E_Fetch_Access_Fault(),
  }

function pmpCheck forall 'n, 'n > 0. (addr: xlenbits, width: atom('n), acc: AccessType(ext_access_type), priv: Privilege)
                  -> option(ExceptionType) = {
  let width : xlenbits = to_bits(sizeof(xlen), width);

  foreach (i from 0 to 63) {
    let prev_pmpaddr = (if i > 0 then pmpReadAddrReg(i - 1) else zeros());
    match pmpMatchEntry(addr, width, acc, priv, pmpcfg_n[i], pmpReadAddrReg(i), prev_pmpaddr) {
      PMP_Success  => { return None(); },
      PMP_Fail     => { return Some(accessToFault(acc)); },
      PMP_Continue => (),
    }
  };
  if priv == Machine then None() else Some(accessToFault(acc))
}

function init_pmp() -> unit = {
  assert(
    sys_pmp_count() == 0 | sys_pmp_count() == 16 | sys_pmp_count() == 64,
    "sys_pmp_count() must be 0, 16, or 64"
  );

  foreach (i from 0 to 63) {
    // On reset the PMP register's A and L bits are set to 0 unless the plaform
    // mandates a different value.
    pmpcfg_n[i] = [pmpcfg_n[i] with A = pmpAddrMatchType_to_bits(OFF), L = 0b0];
  };
}
