/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* default fetch address checks */

type ext_fetch_addr_error = unit

/* Since fetch is done in granules, the check function gets two arguments:
 * start_pc: the PC at the start of the current fetch sequence
 * pc:       the PC for the current granule
 *
 * returns:  the *virtual* memory address to use for the fetch.
 *           any address translation errors are reported for pc, not the returned value.
 */
function ext_fetch_check_pc(start_pc : xlenbits, pc : xlenbits) -> Ext_FetchAddr_Check(ext_fetch_addr_error) =
  Ext_FetchAddr_OK(pc)

function ext_handle_fetch_check_error(err : ext_fetch_addr_error) -> unit =
  ()

/* default control address checks */

type ext_control_addr_error = unit

/* these functions return the address to use as the target for
 * the control transfer.  any address translation or other errors
 * are reported for the original value, not the returned value.
 *
 * NOTE: the input value does *not* have bit[0] set to 0, to enable
 * more accurate bounds checking.  There is no constraint on the output
 * value, which will have bit[0] cleared by the caller if needed.
 */

/* the control address is derived from a non-PC register, e.g. in JALR */
function ext_control_check_addr(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) =
  Ext_ControlAddr_OK(pc)

/* the control address is derived from the PC register, e.g. in JAL */
function ext_control_check_pc(pc : xlenbits) -> Ext_ControlAddr_Check(ext_control_addr_error) =
  Ext_ControlAddr_OK(pc)

function ext_handle_control_check_error(err : ext_control_addr_error) -> unit =
  ()


/* The default data address function does not perform any checks so
   just uses unit for error type. */
type ext_data_addr_error = unit

/* Default data addr is just base register + immediate offset (may be zero).
   Extensions might override and add additional checks. */
function ext_data_get_addr(base : regidx, offset : xlenbits, acc : AccessType(ext_access_type), width : word_width)
         -> Ext_DataAddr_Check(ext_data_addr_error) =
  let addr = X(base) + offset in
  Ext_DataAddr_OK(addr)

function ext_handle_data_check_error(err : ext_data_addr_error) -> unit =
  ()

/* Default implementations of these hooks permit all accesses.  */
function ext_check_phys_mem_read (access_type, paddr, size, aquire, release, reserved, read_meta) =
  Ext_PhysAddr_OK ()

function ext_check_phys_mem_write(write_kind, paddr, size, data, metadata) =
  Ext_PhysAddr_OK ()
