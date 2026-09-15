/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* **************************************************************** */
/* Floating point register file and accessors for F, D extensions   */
/* Floating point CSR and accessors                                 */
/* **************************************************************** */

/* Original version written by Rishiyur S. Nikhil, Sept-Oct 2019    */

/* **************************************************************** */

/* val clause ext_is_CSR_defined : (csreg, Privilege) -> bool */

function clause ext_is_CSR_defined (0x001, _) = haveFExt() | haveZfinx()
function clause ext_is_CSR_defined (0x002, _) = haveFExt() | haveZfinx()
function clause ext_is_CSR_defined (0x003, _) = haveFExt() | haveZfinx()

function clause ext_read_CSR (0x001) = Some(zero_extend(fcsr[FFLAGS]))
function clause ext_read_CSR (0x002) = Some(zero_extend(fcsr[FRM]))
function clause ext_read_CSR (0x003) = Some(zero_extend(fcsr.bits))

function clause ext_write_CSR (0x001, value) = { ext_write_fcsr(fcsr[FRM], value[4..0]); Some(zero_extend(fcsr[FFLAGS])) }
function clause ext_write_CSR (0x002, value) = { ext_write_fcsr(value[2..0], fcsr[FFLAGS]); Some(zero_extend(fcsr[FRM])) }
function clause ext_write_CSR (0x003, value) = { ext_write_fcsr(value[7..5], value[4..0]); Some(zero_extend(fcsr.bits)) }

/* **************************************************************** */
