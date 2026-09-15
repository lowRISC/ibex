/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Extensions may wish to interpose on fetch, control transfer, and data
 * addresses used to access memory and perhaps modify them.  This file
 * defines the return values used by functions that perform this interposition.
 *
 * The model defines defaults for these functions in riscv_addr_checks.sail;
 * extensions would need to define their own functions to override them.
 */

union Ext_FetchAddr_Check ('a : Type) = {
  Ext_FetchAddr_OK  : xlenbits,  /* PC value to use for the actual fetch */
  Ext_FetchAddr_Error : 'a
}

union Ext_ControlAddr_Check ('a : Type) = {
  Ext_ControlAddr_OK : xlenbits, /* PC value to use for the target of the control operation */
  Ext_ControlAddr_Error : 'a
}

union Ext_DataAddr_Check ('a : Type) = {
  Ext_DataAddr_OK : xlenbits,    /* Address to use for the data access */
  Ext_DataAddr_Error : 'a
}

union Ext_PhysAddr_Check = {
  Ext_PhysAddr_OK : unit,
  Ext_PhysAddr_Error : ExceptionType
}

/*!
 * Validate a read from physical memory.
 * THIS(access_type, paddr, size, aquire, release, reserved, read_meta) should
 * return Some(exception) to abort the read or None to allow it to proceed. The
 * check is performed after PMP checks and does not apply to MMIO memory.
 */
val ext_check_phys_mem_read : forall 'n, 0 < 'n <= max_mem_access . (AccessType (ext_access_type), xlenbits, atom('n), bool, bool, bool, bool) -> Ext_PhysAddr_Check

/*!
 * Validate a write to physical memory.
 * THIS(write_kind, paddr, size, data, metadata) should return Some(exception)
 * to abort the write or None to allow it to proceed. The check is performed
 * after PMP checks and does not apply to MMIO memory.
 */
val ext_check_phys_mem_write : forall 'n, 0 < 'n <= max_mem_access . (write_kind, xlenbits, atom('n), bits(8 * 'n), mem_meta) -> Ext_PhysAddr_Check
