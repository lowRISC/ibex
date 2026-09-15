/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Shared definitions for supervisor-mode page-table-entries and permission checks.
 *
 * These definitions are independent of xlen and do not involve
 * accessing physical memory.
 */

/* PageSize */

let PAGESIZE_BITS = 12

/*
 * Definitions for RV32, which has a single address translation mode: Sv32.
 */

type vaddr32 = bits(32)
type paddr32 = bits(34)
type pte32   = bits(32)

/* asid */
type asid32 = bits(9)

function curAsid32(satp : bits(32)) -> asid32 = {
  let s = Mk_Satp32(satp);
  s[Asid]
}

/* page table base from satp */
function curPTB32(satp : bits(32)) -> paddr32 = {
  let s : Satp32 = Mk_Satp32(satp);
  shiftl(zero_extend(s[PPN]), PAGESIZE_BITS)
}

/* Sv32 parameters and bitfield layouts */

let SV32_LEVEL_BITS = 10
let SV32_LEVELS     = 2
let PTE32_LOG_SIZE  = 2
let PTE32_SIZE      = 4

bitfield SV32_Vaddr : vaddr32 = {
  VPNi  : 31 .. 12,
  PgOfs : 11 .. 0
}

bitfield SV32_Paddr : paddr32 = {
  PPNi  : 33 .. 12,
  PgOfs : 11 .. 0
}

bitfield SV32_PTE : pte32 = {
  PPNi  : 31 .. 10,
  RSW   : 9  .. 8,
  BITS  : 7  .. 0
}

/*
 * Definitions for RV64, which has two defined address translation modes: Sv39 and Sv48.
 */

/* Sv48 and Sv64 are reserved but not defined.  The size of the VPN
 * increases by 9 bits through Sv39, Sv48 and Sv57, but not for Sv64.
 * Also, the 45-bit size of the VPN for Sv57 exceeds the 44-bit size
 * of the PPN in satp64.  Due to these corner cases, it is unlikely
 * that definitions can be shared across all four schemes, so separate
 * definitions might eventually be needed for each translation mode.
 *
 * But to keep things simple for now, since Sv39 and Sv48 have the
 * same PPN size, we share some definitions.
 */

type paddr64 = bits(56)
type pte64   = bits(64)

/* asid */

type asid64 = bits(16)

function curAsid64(satp : bits(64)) -> asid64 = {
  let s = Mk_Satp64(satp);
  s[Asid]
}

/* page table base from satp */
function curPTB64(satp : bits(64)) -> paddr64 = {
  let s = Mk_Satp64(satp);
  shiftl(zero_extend(s[PPN]), PAGESIZE_BITS)
}

/* Sv39 parameters and bitfield layouts */

let SV39_LEVEL_BITS = 9
let SV39_LEVELS     = 3
let PTE39_LOG_SIZE  = 3
let PTE39_SIZE      = 8

type vaddr39 = bits(39)

bitfield SV39_Vaddr : vaddr39 = {
  VPNi  : 38 .. 12,
  PgOfs : 11 .. 0
}

bitfield SV39_Paddr : paddr64 = {
  PPNi  : 55 .. 12,
  PgOfs : 11 .. 0
}

bitfield SV39_PTE : pte64 = {
  Ext   : 63 .. 54,
  PPNi  : 53 .. 10,
  RSW   : 9  .. 8,
  BITS  : 7  .. 0
}

/* Sv48 parameters and bitfield layouts */

let SV48_LEVEL_BITS = 9
let SV48_LEVELS     = 4
let PTE48_LOG_SIZE  = 3
let PTE48_SIZE      = 8

type vaddr48 = bits(48)
type pte48   = bits(64)

bitfield SV48_Vaddr : vaddr48 = {
  VPNi  : 47 .. 12,
  PgOfs : 11 .. 0
}

bitfield SV48_Paddr : paddr64 = {
  PPNi  : 55 .. 12,
  PgOfs : 11 .. 0
}

bitfield SV48_PTE : pte48 = {
  Ext   : 63 .. 54,
  PPNi  : 53 .. 10,
  RSW   : 9  .. 8,
  BITS  : 7  .. 0
}

/* The types below are parameterized by 'paddr and 'pte to support
 * various architectural widths (e.g. RV32, RV64).  ext_ptw supports
 * extensions to the default address translation and page-table-walk.
 */

/* Result of a page-table walk.  */

union PTW_Result('paddr : Type, 'pte : Type) = {
  PTW_Success: ('paddr, 'pte, 'paddr, nat, bool, ext_ptw),
  PTW_Failure: (PTW_Error, ext_ptw)
}

/* Result of address translation */

union TR_Result('paddr : Type, 'failure : Type) = {
  TR_Address : ('paddr, ext_ptw),
  TR_Failure : ('failure, ext_ptw)
}
