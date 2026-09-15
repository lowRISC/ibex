/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* idealized generic TLB entry to model fence.vm and also speed up simulation. */

struct TLB_Entry('asidlen: Int, 'valen: Int, 'palen: Int, 'ptelen: Int) = {
  asid : bits('asidlen),
  global : bool,
  vAddr : bits('valen),      /* VPN */
  pAddr : bits('palen),      /* PPN */
  vMatchMask : bits('valen), /* matching mask for superpages */
  vAddrMask  : bits('valen), /* selection mask for superpages */
  pte : bits('ptelen),       /* PTE */
  pteAddr : bits('palen),    /* for dirty writeback */
  age : bits(64)
}


val make_TLB_Entry : forall 'asidlen 'valen 'palen 'ptelen, 'valen > 0.
  (bits('asidlen), bool, bits('valen), bits('palen), bits('ptelen), nat, bits('palen), nat)
  -> TLB_Entry('asidlen, 'valen, 'palen, 'ptelen)
function make_TLB_Entry(asid, global, vAddr, pAddr, pte, level, pteAddr, levelBitSize) = {
  let shift : nat = PAGESIZE_BITS + (level * levelBitSize);
  /* fixme hack: use a better idiom for masks */
  let vAddrMask  : bits('valen) = shiftl(vAddr ^ vAddr ^ zero_extend(0b1), shift) - 1;
  let vMatchMask : bits('valen) = ~ (vAddrMask);
  struct {
    asid = asid,
    global = global,
    pte = pte,
    pteAddr = pteAddr,
    vAddrMask = vAddrMask,
    vMatchMask = vMatchMask,
    vAddr = vAddr & vMatchMask,
    pAddr = shiftl(shiftr(pAddr, shift), shift),
    age = mcycle
  }
}

val match_TLB_Entry : forall 'asidlen 'valen 'palen 'ptelen.
  (TLB_Entry('asidlen, 'valen, 'palen, 'ptelen), bits('asidlen), bits('valen))
  -> bool
function match_TLB_Entry(ent, asid, vaddr) =
  (ent.global | (ent.asid == asid)) & (ent.vAddr == (ent.vMatchMask & vaddr))

val flush_TLB_Entry : forall 'asidlen 'valen 'palen 'ptelen.
  (TLB_Entry('asidlen, 'valen, 'palen, 'ptelen), option(bits('asidlen)), option(bits('valen)))
  -> bool
function flush_TLB_Entry(e, asid, addr) = {
  match(asid, addr) {
    ( None(),  None()) => true,
    ( None(), Some(a)) => e.vAddr == (e.vMatchMask & a),
    (Some(i),  None()) => (e.asid == i) & not(e.global),
    (Some(i), Some(a)) => (  (e.asid == i) & (e.vAddr == (a & e.vMatchMask))
                           & not(e.global))
  }
}
