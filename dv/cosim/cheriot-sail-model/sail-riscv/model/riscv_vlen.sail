/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

register elen : bits(1)

val get_elen_pow : unit -> {|5, 6|}

function get_elen_pow() = match elen {
    0b0 => 5,
    0b1 => 6
}
/* Note: ELEN=32 requires a different encoding of the CSR vtype.
 * The current version of vtype implementation corresponds to the ELEN=64 configuration.
 * TODO: the configurarion of ELEN and its corresponding vtype implementations.
 */

register vlen : bits(4)

val get_vlen_pow : unit -> {|5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16|}

function get_vlen_pow() = match vlen {
    0b0000 => 5,
    0b0001 => 6,
    0b0010 => 7,
    0b0011 => 8,
    0b0100 => 9,
    0b0101 => 10,
    0b0110 => 11,
    0b0111 => 12,
    0b1000 => 13,
    0b1001 => 14,
    0b1010 => 15,
    _      => 16
}

type vlenmax : Int = 65536

/* Note: At present, the values of elen and vlen need to be manually speficied
 * in the init_sys() function of riscv_sys_control.sail before compiling the emulators,
 * e.g.,
 *  vlen = 0b0101;
 *  elen = 0b1;
 * means VLEN = 1024 and ELEN = 64,
 * They will be configurable when user-specified configuration is supported in Sail.
 *
 * Also, VLEN >= ELEN must be satisfied and this condition check should be added
 * after their initialization.
 */
