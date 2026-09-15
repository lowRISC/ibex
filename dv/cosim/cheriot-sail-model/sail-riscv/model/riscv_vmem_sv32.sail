/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Sv32 address translation for RV32. */

/* FIXME: paddr32 is 34-bits, but phys_mem accesses in riscv_mem take 32-bit (xlenbits) addresses.
 * Define a converter for now.
 */

function to_phys_addr(a : paddr32) -> xlenbits = a[31..0]

val walk32 : (vaddr32, AccessType(ext_access_type), Privilege, bool, bool, paddr32, nat, bool, ext_ptw) -> PTW_Result(paddr32, SV32_PTE)
function walk32(vaddr, ac, priv, mxr, do_sum, ptb, level, global, ext_ptw) = {
  let va = Mk_SV32_Vaddr(vaddr);
  let pt_ofs : paddr32 = shiftl(zero_extend(shiftr(va[VPNi], (level * SV32_LEVEL_BITS))[(SV32_LEVEL_BITS - 1) .. 0]),
                                PTE32_LOG_SIZE);
  let pte_addr = ptb + pt_ofs;
  match (mem_read_priv(Read(Data), Supervisor, to_phys_addr(pte_addr), 4, false, false, false)) {
    MemException(_) => {
/*    print("walk32(vaddr=" ^ BitStr(vaddr) ^ " level=" ^ dec_str(level)
            ^ " pt_base=" ^ BitStr(to_phys_addr(ptb))
            ^ " pt_ofs=" ^ BitStr(to_phys_addr(pt_ofs))
            ^ " pte_addr=" ^ BitStr(to_phys_addr(pte_addr))
            ^ ": invalid pte address"); */
      PTW_Failure(PTW_Access(), ext_ptw)
    },
    MemValue(v) => {
      let pte = Mk_SV32_PTE(v);
      let pbits = pte[BITS];
      let ext_pte : extPte = default_sv32_ext_pte;
      let pattr = Mk_PTE_Bits(pbits);
      let is_global = global | (pattr[G] == 0b1);
/*    print("walk32(vaddr=" ^ BitStr(vaddr) ^ " level=" ^ dec_str(level)
            ^ " pt_base=" ^ BitStr(to_phys_addr(ptb))
            ^ " pt_ofs=" ^ BitStr(to_phys_addr(pt_ofs))
            ^ " pte_addr=" ^ BitStr(to_phys_addr(pte_addr))
            ^ " pte=" ^ BitStr(v)); */
      if isInvalidPTE(pbits, ext_pte) then {
/*      print("walk32: invalid pte"); */
        PTW_Failure(PTW_Invalid_PTE(), ext_ptw)
      } else {
        if isPTEPtr(pbits, ext_pte) then {
          if level > 0 then {
            /* walk down the pointer to the next level */
            walk32(vaddr, ac, priv, mxr, do_sum, shiftl(zero_extend(pte[PPNi]), PAGESIZE_BITS), level - 1, is_global, ext_ptw)
          } else {
            /* last-level PTE contains a pointer instead of a leaf */
/*          print("walk32: last-level pte contains a ptr"); */
            PTW_Failure(PTW_Invalid_PTE(), ext_ptw)
          }
        } else { /* leaf PTE */
          match checkPTEPermission(ac, priv, mxr, do_sum, pattr, ext_pte, ext_ptw) {
            PTE_Check_Failure(ext_ptw, ext_ptw_fail) => {
/*            print("walk32: pte permission check failure"); */
              PTW_Failure(ext_get_ptw_error(ext_ptw_fail), ext_ptw)
            },
            PTE_Check_Success(ext_ptw) => {
              if level > 0 then { /* superpage */
                /* fixme hack: to get a mask of appropriate size */
                let mask = shiftl(pte[PPNi] ^ pte[PPNi] ^ zero_extend(0b1), level * SV32_LEVEL_BITS) - 1;
                if (pte[PPNi] & mask) != zero_extend(0b0) then {
                  /* misaligned superpage mapping */
/*                print("walk32: misaligned superpage mapping"); */
                  PTW_Failure(PTW_Misaligned(), ext_ptw)
                } else {
                  /* add the appropriate bits of the VPN to the superpage PPN */
                  let ppn = pte[PPNi] | (zero_extend(va[VPNi]) & mask);
/*                let res = append(ppn, va[PgOfs]);
                  print("walk32: using superpage: pte.ppn=" ^ BitStr(pte[PPNi])
                        ^ " ppn=" ^ BitStr(ppn) ^ " res=" ^ BitStr(res)); */
                  PTW_Success(append(ppn, va[PgOfs]), pte, pte_addr, level, is_global, ext_ptw)
                }
              } else {
                /* normal leaf PTE */
/*              let res = append(pte[PPNi], va[PgOfs]);
                print("walk32: pte.ppn=" ^ BitStr(pte[PPNi]) ^ " ppn=" ^ BitStr(pte[PPNi]) ^ " res=" ^ BitStr(res)); */
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
// type TLB32_Entry = TLB_Entry(sizeof(asid32), sizeof(vaddr32), sizeof(paddr32), sizeof(pte32))
type TLB32_Entry = TLB_Entry(9, 32, 34, 32)
register tlb32 : option(TLB32_Entry)

val lookup_TLB32 : (asid32, vaddr32) -> option((nat, TLB32_Entry))
function lookup_TLB32(asid, vaddr) =
  match tlb32 {
    None()  => None(),
    Some(e) => if match_TLB_Entry(e, asid, vaddr) then Some((0, e)) else None()
  }

val add_to_TLB32 : (asid32, vaddr32, paddr32, SV32_PTE, paddr32, nat, bool) -> unit
function add_to_TLB32(asid, vAddr, pAddr, pte, pteAddr, level, global) = {
  let ent : TLB32_Entry = make_TLB_Entry(asid, global, vAddr, pAddr, pte.bits, level, pteAddr, SV32_LEVEL_BITS);
  tlb32 = Some(ent)
}

function write_TLB32(idx : nat, ent : TLB32_Entry) -> unit =
  tlb32 = Some(ent)

val flush_TLB32 : (option(asid32), option(vaddr32)) -> unit
function flush_TLB32(asid, addr) =
  match (tlb32) {
    None()  => (),
    Some(e) => if   flush_TLB_Entry(e, asid, addr)
               then tlb32 = None()
               else ()
  }

/* address translation */

val translate32 : (asid32, paddr32, vaddr32, AccessType(ext_access_type), Privilege, bool, bool, nat, ext_ptw) -> TR_Result(paddr32, PTW_Error)
function translate32(asid, ptb, vAddr, ac, priv, mxr, do_sum, level, ext_ptw) = {
  match lookup_TLB32(asid, vAddr) {
    Some(idx, ent) => {
/*    print("translate32: TLB32 hit for " ^ BitStr(vAddr)); */
      let  pte = Mk_SV32_PTE(ent.pte);
      let  ext_pte : extPte = zeros(); // no reserved bits for extensions
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
                /* ext is unused since there are no reserved bits for extensions */
                n_ent : TLB32_Entry = ent;
                n_ent.pte = n_pte.bits;
                write_TLB32(idx, n_ent);
                /* update page table */
                match mem_write_value_priv(to_phys_addr(zero_extend(ent.pteAddr)), 4, n_pte.bits, Supervisor, false, false, false) {
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
      match walk32(vAddr, ac, priv, mxr, do_sum, ptb, level, false, ext_ptw) {
        PTW_Failure(f, ext_ptw) => TR_Failure(f, ext_ptw),
        PTW_Success(pAddr, pte, pteAddr, level, global, ext_ptw) => {
          match update_PTE_Bits(Mk_PTE_Bits(pte[BITS]), ac, zeros()) {
            None() => {
              add_to_TLB32(asid, vAddr, pAddr, pte, pteAddr, level, global);
              TR_Address(pAddr, ext_ptw)
            },
            Some(pbits, ext) =>
              if not(plat_enable_dirty_update())
              then {
                /* pte needs dirty/accessed update but that is not enabled */
                TR_Failure(PTW_PTE_Update(), ext_ptw)
              } else {
                var w_pte : SV32_PTE = update_BITS(pte, pbits.bits);
                /* ext is unused since there are no reserved bits for extensions */
                match mem_write_value_priv(to_phys_addr(pteAddr), 4, w_pte.bits, Supervisor, false, false, false) {
                  MemValue(_) => {
                    add_to_TLB32(asid, vAddr, pAddr, w_pte, pteAddr, level, global);
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

function init_vmem_sv32() -> unit = {
  tlb32 = None()
}
