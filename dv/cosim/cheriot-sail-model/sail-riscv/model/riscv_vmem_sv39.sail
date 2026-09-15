/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Sv39 address translation for RV64. */

val walk39 : (vaddr39, AccessType(ext_access_type), Privilege, bool, bool, paddr64, nat, bool, ext_ptw) -> PTW_Result(paddr64, SV39_PTE)
function walk39(vaddr, ac, priv, mxr, do_sum, ptb, level, global, ext_ptw) = {
  let va = Mk_SV39_Vaddr(vaddr);
  let pt_ofs : paddr64 = shiftl(zero_extend(shiftr(va[VPNi], (level * SV39_LEVEL_BITS))[(SV39_LEVEL_BITS - 1) .. 0]),
                                PTE39_LOG_SIZE);
  let pte_addr = ptb + pt_ofs;
  match (mem_read_priv(Read(Data), Supervisor, zero_extend(pte_addr), 8, false, false, false)) {
    MemException(_) => {
/*    print("walk39(vaddr=" ^ BitStr(vaddr) ^ " level=" ^ dec_str(level)
            ^ " pt_base=" ^ BitStr(ptb)
            ^ " pt_ofs=" ^ BitStr(pt_ofs)
            ^ " pte_addr=" ^ BitStr(pte_addr)
            ^ ": invalid pte address"); */
      PTW_Failure(PTW_Access(), ext_ptw)
    },
    MemValue(v) => {
      let pte = Mk_SV39_PTE(v);
      let pbits = pte[BITS];
      let ext_pte = pte[Ext];
      let pattr = Mk_PTE_Bits(pbits);
      let is_global = global | (pattr[G] == 0b1);
/*    print("walk39(vaddr=" ^ BitStr(vaddr) ^ " level=" ^ dec_str(level)
            ^ " pt_base=" ^ BitStr(ptb)
            ^ " pt_ofs=" ^ BitStr(pt_ofs)
            ^ " pte_addr=" ^ BitStr(pte_addr)
            ^ " pte=" ^ BitStr(v)); */
      if isInvalidPTE(pbits, ext_pte) then {
/*      print("walk39: invalid pte"); */
        PTW_Failure(PTW_Invalid_PTE(), ext_ptw)
      } else {
        if isPTEPtr(pbits, ext_pte) then {
          if level > 0 then {
            /* walk down the pointer to the next level */
            walk39(vaddr, ac, priv, mxr, do_sum, shiftl(zero_extend(pte[PPNi]), PAGESIZE_BITS), level - 1, is_global, ext_ptw)
          } else {
            /* last-level PTE contains a pointer instead of a leaf */
/*          print("walk39: last-level pte contains a ptr"); */
            PTW_Failure(PTW_Invalid_PTE(), ext_ptw)
          }
        } else { /* leaf PTE */
          match checkPTEPermission(ac, priv, mxr, do_sum, pattr, ext_pte, ext_ptw) {
            PTE_Check_Failure(ext_ptw, ext_ptw_fail) => {
/*            print("walk39: pte permission check failure"); */
              PTW_Failure(ext_get_ptw_error(ext_ptw_fail), ext_ptw)
            },
            PTE_Check_Success(ext_ptw)  => {
              if level > 0 then { /* superpage */
                /* fixme hack: to get a mask of appropriate size */
                let mask = shiftl(pte[PPNi] ^ pte[PPNi] ^ zero_extend(0b1), level * SV39_LEVEL_BITS) - 1;
                if (pte[PPNi] & mask) != zero_extend(0b0) then {
                  /* misaligned superpage mapping */
/*                print("walk39: misaligned superpage mapping"); */
                  PTW_Failure(PTW_Misaligned(), ext_ptw)
                } else {
                  /* add the appropriate bits of the VPN to the superpage PPN */
                  let ppn = pte[PPNi] | (zero_extend(va[VPNi]) & mask);
/*                let res = append(ppn, va[PgOfs]);
                  print("walk39: using superpage: pte.ppn=" ^ BitStr(pte[PPNi])
                        ^ " ppn=" ^ BitStr(ppn) ^ " res=" ^ BitStr(res)); */
                  PTW_Success(append(ppn, va[PgOfs]), pte, pte_addr, level, is_global, ext_ptw)
                }
              } else {
                /* normal leaf PTE */
/*              let res = append(pte[PPNi], va[PgOfs]);
                print("walk39: pte.ppn=" ^ BitStr(pte[PPNi]) ^ " ppn=" ^ BitStr(pte[PPNi]) ^ " res=" ^ BitStr(res)); */
                PTW_Success(append(pte[PPNi], va[PgOfs]), pte, pte_addr, level, is_global, ext_ptw)
              }
            }
          }
        }
      }
    }
  }
}

/* TLB management: single entry for now */

// ideally we would use the below form:
// type TLB39_Entry = TLB_Entry(sizeof(asid64), sizeof(vaddr39), sizeof(paddr64), sizeof(pte64))
type TLB39_Entry = TLB_Entry(16, 39, 56, 64)
register tlb39 : option(TLB39_Entry)

val lookup_TLB39 : (asid64, vaddr39) -> option((nat, TLB39_Entry))
function lookup_TLB39(asid, vaddr) =
  match tlb39 {
    None()  => None(),
    Some(e) => if match_TLB_Entry(e, asid, vaddr) then Some((0, e)) else None()
  }

val add_to_TLB39 : (asid64, vaddr39, paddr64, SV39_PTE, paddr64, nat, bool) -> unit
function add_to_TLB39(asid, vAddr, pAddr, pte, pteAddr, level, global) = {
  let ent : TLB39_Entry = make_TLB_Entry(asid, global, vAddr, pAddr, pte.bits, level, pteAddr, SV39_LEVEL_BITS);
  tlb39 = Some(ent)
}

function write_TLB39(idx : nat, ent : TLB39_Entry) -> unit =
  tlb39 = Some(ent)

val flush_TLB39 : (option(asid64), option(vaddr39)) -> unit
function flush_TLB39(asid, addr) =
  match (tlb39) {
    None()  => (),
    Some(e) => if   flush_TLB_Entry(e, asid, addr)
               then tlb39 = None()
               else ()
  }

/* address translation */

val translate39 : (asid64, paddr64, vaddr39, AccessType(ext_access_type), Privilege, bool, bool, nat, ext_ptw) -> TR_Result(paddr64, PTW_Error)
function translate39(asid, ptb, vAddr, ac, priv, mxr, do_sum, level, ext_ptw) = {
  match lookup_TLB39(asid, vAddr) {
    Some(idx, ent) => {
/*    print("translate39: TLB39 hit for " ^ BitStr(vAddr)); */
      let  pte = Mk_SV39_PTE(ent.pte);
      let  ext_pte = pte[Ext];
      let  pteBits = Mk_PTE_Bits(pte[BITS]);
      match checkPTEPermission(ac, priv, mxr, do_sum, pteBits, ext_pte, ext_ptw) {
        PTE_Check_Failure(ext_ptw, ext_ptw_fail) => { TR_Failure(ext_get_ptw_error(ext_ptw_fail), ext_ptw) },
        PTE_Check_Success(ext_ptw) => {
          match update_PTE_Bits(pteBits, ac, ext_pte) {
            None()           => TR_Address(ent.pAddr | zero_extend(vAddr & ent.vAddrMask), ext_ptw),
            Some(pbits, ext) => {
              if not(plat_enable_dirty_update())
              then {
                /* pte needs dirty/accessed update but that is not enabled */
                TR_Failure(PTW_PTE_Update(), ext_ptw)
              } else {
                /* update PTE entry and TLB */
                n_pte = update_BITS(pte, pbits.bits);
                n_pte = update_Ext(n_pte, ext);
                n_ent : TLB39_Entry = ent;
                n_ent.pte = n_pte.bits;
                write_TLB39(idx, n_ent);
                /* update page table */
                match mem_write_value_priv(zero_extend(ent.pteAddr), 8, n_pte.bits, Supervisor, false, false, false) {
                  MemValue(_)     => (),
                  MemException(e) => internal_error(__FILE__, __LINE__, "invalid physical address in TLB")
                };
                TR_Address(ent.pAddr | zero_extend(vAddr & ent.vAddrMask), ext_ptw)
              }
            }
          }
        }
      }
    },
    None() => {
      match walk39(vAddr, ac, priv, mxr, do_sum, ptb, level, false, ext_ptw) {
        PTW_Failure(f, ext_ptw) => TR_Failure(f, ext_ptw),
        PTW_Success(pAddr, pte, pteAddr, level, global, ext_ptw) => {
          match update_PTE_Bits(Mk_PTE_Bits(pte[BITS]), ac, pte[Ext]) {
            None() => {
              add_to_TLB39(asid, vAddr, pAddr, pte, pteAddr, level, global);
              TR_Address(pAddr, ext_ptw)
            },
            Some(pbits, ext) =>
              if not(plat_enable_dirty_update())
              then {
                /* pte needs dirty/accessed update but that is not enabled */
                TR_Failure(PTW_PTE_Update(), ext_ptw)
              } else {
                var w_pte : SV39_PTE = update_BITS(pte, pbits.bits);
                w_pte = update_Ext(w_pte, ext);
                match mem_write_value_priv(zero_extend(pteAddr), 8, w_pte.bits, Supervisor, false, false, false) {
                  MemValue(_) => {
                    add_to_TLB39(asid, vAddr, pAddr, w_pte, pteAddr, level, global);
                    TR_Address(pAddr, ext_ptw)
                  },
                  MemException(e) => {
                    /* pte is not in valid memory */
                    TR_Failure(PTW_Access(), ext_ptw)
                  }
                }
              }
          }
        }
      }
    }
  }
}

function init_vmem_sv39() -> unit = {
  tlb39 = None()
}
