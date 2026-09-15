/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* Mapping of csr addresses to their names. */

val csr_name_map : csreg <-> string

scattered mapping csr_name_map

/* user trap setup */
mapping clause csr_name_map = 0x000  <-> "ustatus"
mapping clause csr_name_map = 0x004  <-> "uie"
mapping clause csr_name_map = 0x005  <-> "utvec"
/* user trap handling */
mapping clause csr_name_map = 0x040  <-> "uscratch"
mapping clause csr_name_map = 0x041  <-> "uepc"
mapping clause csr_name_map = 0x042  <-> "ucause"
mapping clause csr_name_map = 0x043  <-> "utval"
mapping clause csr_name_map = 0x044  <-> "uip"
/* user floating-point context */
mapping clause csr_name_map = 0x001  <-> "fflags"
mapping clause csr_name_map = 0x002  <-> "frm"
mapping clause csr_name_map = 0x003  <-> "fcsr"
/* user entropy source */
mapping clause csr_name_map = 0x015  <-> "seed"
/* counter/timers */
mapping clause csr_name_map = 0xC00  <-> "cycle"
mapping clause csr_name_map = 0xC01  <-> "time"
mapping clause csr_name_map = 0xC02  <-> "instret"
mapping clause csr_name_map = 0xC80  <-> "cycleh"
mapping clause csr_name_map = 0xC81  <-> "timeh"
mapping clause csr_name_map = 0xC82  <-> "instreth"
/* TODO: other hpm counters */
/* supervisor trap setup */
mapping clause csr_name_map = 0x100  <-> "sstatus"
mapping clause csr_name_map = 0x102  <-> "sedeleg"
mapping clause csr_name_map = 0x103  <-> "sideleg"
mapping clause csr_name_map = 0x104  <-> "sie"
mapping clause csr_name_map = 0x105  <-> "stvec"
mapping clause csr_name_map = 0x106  <-> "scounteren"
/* supervisor trap handling */
mapping clause csr_name_map = 0x140  <-> "sscratch"
mapping clause csr_name_map = 0x141  <-> "sepc"
mapping clause csr_name_map = 0x142  <-> "scause"
mapping clause csr_name_map = 0x143  <-> "stval"
mapping clause csr_name_map = 0x144  <-> "sip"
/* supervisor protection and translation */
mapping clause csr_name_map = 0x180  <-> "satp"
/* supervisor envcfg */
mapping clause csr_name_map = 0x10A  <-> "senvcfg"
/* machine information registers */
mapping clause csr_name_map = 0xF11  <-> "mvendorid"
mapping clause csr_name_map = 0xF12  <-> "marchid"
mapping clause csr_name_map = 0xF13  <-> "mimpid"
mapping clause csr_name_map = 0xF14  <-> "mhartid"
/* machine trap setup */
mapping clause csr_name_map = 0x300  <-> "mstatus"
mapping clause csr_name_map = 0x301  <-> "misa"
mapping clause csr_name_map = 0x302  <-> "medeleg"
mapping clause csr_name_map = 0x303  <-> "mideleg"
mapping clause csr_name_map = 0x304  <-> "mie"
mapping clause csr_name_map = 0x305  <-> "mtvec"
mapping clause csr_name_map = 0x306  <-> "mcounteren"
mapping clause csr_name_map = 0x320  <-> "mcountinhibit"
/* machine envcfg */
mapping clause csr_name_map = 0x30A  <-> "menvcfg"
/* machine trap handling */
mapping clause csr_name_map = 0x340  <-> "mscratch"
mapping clause csr_name_map = 0x341  <-> "mepc"
mapping clause csr_name_map = 0x342  <-> "mcause"
mapping clause csr_name_map = 0x343  <-> "mtval"
mapping clause csr_name_map = 0x344  <-> "mip"
/* machine protection and translation */
mapping clause csr_name_map = 0x3A0  <-> "pmpcfg0"
mapping clause csr_name_map = 0x3A1  <-> "pmpcfg1"
mapping clause csr_name_map = 0x3A2  <-> "pmpcfg2"
mapping clause csr_name_map = 0x3A3  <-> "pmpcfg3"
mapping clause csr_name_map = 0x3A4  <-> "pmpcfg4"
mapping clause csr_name_map = 0x3A5  <-> "pmpcfg5"
mapping clause csr_name_map = 0x3A6  <-> "pmpcfg6"
mapping clause csr_name_map = 0x3A7  <-> "pmpcfg7"
mapping clause csr_name_map = 0x3A8  <-> "pmpcfg8"
mapping clause csr_name_map = 0x3A9  <-> "pmpcfg9"
mapping clause csr_name_map = 0x3AA  <-> "pmpcfg10"
mapping clause csr_name_map = 0x3AB  <-> "pmpcfg11"
mapping clause csr_name_map = 0x3AC  <-> "pmpcfg12"
mapping clause csr_name_map = 0x3AD  <-> "pmpcfg13"
mapping clause csr_name_map = 0x3AE  <-> "pmpcfg14"
mapping clause csr_name_map = 0x3AF  <-> "pmpcfg15"
mapping clause csr_name_map = 0x3B0  <-> "pmpaddr0"
mapping clause csr_name_map = 0x3B1  <-> "pmpaddr1"
mapping clause csr_name_map = 0x3B2  <-> "pmpaddr2"
mapping clause csr_name_map = 0x3B3  <-> "pmpaddr3"
mapping clause csr_name_map = 0x3B4  <-> "pmpaddr4"
mapping clause csr_name_map = 0x3B5  <-> "pmpaddr5"
mapping clause csr_name_map = 0x3B6  <-> "pmpaddr6"
mapping clause csr_name_map = 0x3B7  <-> "pmpaddr7"
mapping clause csr_name_map = 0x3B8  <-> "pmpaddr8"
mapping clause csr_name_map = 0x3B9  <-> "pmpaddr9"
mapping clause csr_name_map = 0x3BA  <-> "pmpaddr10"
mapping clause csr_name_map = 0x3BB  <-> "pmpaddr11"
mapping clause csr_name_map = 0x3BC  <-> "pmpaddr12"
mapping clause csr_name_map = 0x3BD  <-> "pmpaddr13"
mapping clause csr_name_map = 0x3BE  <-> "pmpaddr14"
mapping clause csr_name_map = 0x3BF  <-> "pmpaddr15"
mapping clause csr_name_map = 0x3C0  <-> "pmpaddr16"
mapping clause csr_name_map = 0x3C1  <-> "pmpaddr17"
mapping clause csr_name_map = 0x3C2  <-> "pmpaddr18"
mapping clause csr_name_map = 0x3C3  <-> "pmpaddr19"
mapping clause csr_name_map = 0x3C4  <-> "pmpaddr20"
mapping clause csr_name_map = 0x3C5  <-> "pmpaddr21"
mapping clause csr_name_map = 0x3C6  <-> "pmpaddr22"
mapping clause csr_name_map = 0x3C7  <-> "pmpaddr23"
mapping clause csr_name_map = 0x3C8  <-> "pmpaddr24"
mapping clause csr_name_map = 0x3C9  <-> "pmpaddr25"
mapping clause csr_name_map = 0x3CA  <-> "pmpaddr26"
mapping clause csr_name_map = 0x3CB  <-> "pmpaddr27"
mapping clause csr_name_map = 0x3CC  <-> "pmpaddr28"
mapping clause csr_name_map = 0x3CD  <-> "pmpaddr29"
mapping clause csr_name_map = 0x3CE  <-> "pmpaddr30"
mapping clause csr_name_map = 0x3CF  <-> "pmpaddr31"
mapping clause csr_name_map = 0x3D0  <-> "pmpaddr32"
mapping clause csr_name_map = 0x3D1  <-> "pmpaddr33"
mapping clause csr_name_map = 0x3D2  <-> "pmpaddr34"
mapping clause csr_name_map = 0x3D3  <-> "pmpaddr35"
mapping clause csr_name_map = 0x3D4  <-> "pmpaddr36"
mapping clause csr_name_map = 0x3D5  <-> "pmpaddr37"
mapping clause csr_name_map = 0x3D6  <-> "pmpaddr38"
mapping clause csr_name_map = 0x3D7  <-> "pmpaddr39"
mapping clause csr_name_map = 0x3D8  <-> "pmpaddr40"
mapping clause csr_name_map = 0x3D9  <-> "pmpaddr41"
mapping clause csr_name_map = 0x3DA  <-> "pmpaddr42"
mapping clause csr_name_map = 0x3DB  <-> "pmpaddr43"
mapping clause csr_name_map = 0x3DC  <-> "pmpaddr44"
mapping clause csr_name_map = 0x3DD  <-> "pmpaddr45"
mapping clause csr_name_map = 0x3DE  <-> "pmpaddr46"
mapping clause csr_name_map = 0x3DF  <-> "pmpaddr47"
mapping clause csr_name_map = 0x3E0  <-> "pmpaddr48"
mapping clause csr_name_map = 0x3E1  <-> "pmpaddr49"
mapping clause csr_name_map = 0x3E2  <-> "pmpaddr50"
mapping clause csr_name_map = 0x3E3  <-> "pmpaddr51"
mapping clause csr_name_map = 0x3E4  <-> "pmpaddr52"
mapping clause csr_name_map = 0x3E5  <-> "pmpaddr53"
mapping clause csr_name_map = 0x3E6  <-> "pmpaddr54"
mapping clause csr_name_map = 0x3E7  <-> "pmpaddr55"
mapping clause csr_name_map = 0x3E8  <-> "pmpaddr56"
mapping clause csr_name_map = 0x3E9  <-> "pmpaddr57"
mapping clause csr_name_map = 0x3EA  <-> "pmpaddr58"
mapping clause csr_name_map = 0x3EB  <-> "pmpaddr59"
mapping clause csr_name_map = 0x3EC  <-> "pmpaddr60"
mapping clause csr_name_map = 0x3ED  <-> "pmpaddr61"
mapping clause csr_name_map = 0x3EE  <-> "pmpaddr62"
mapping clause csr_name_map = 0x3EF  <-> "pmpaddr63"
/* machine counters/timers */
mapping clause csr_name_map = 0xB00  <-> "mcycle"
mapping clause csr_name_map = 0xB02  <-> "minstret"
mapping clause csr_name_map = 0xB80  <-> "mcycleh"
mapping clause csr_name_map = 0xB82  <-> "minstreth"
/* TODO: other hpm counters and events */
/* trigger/debug */
mapping clause csr_name_map = 0x7a0  <-> "tselect"
mapping clause csr_name_map = 0x7a1  <-> "tdata1"
mapping clause csr_name_map = 0x7a2  <-> "tdata2"
mapping clause csr_name_map = 0x7a3  <-> "tdata3"
/* vector csrs */
mapping clause csr_name_map = 0x008  <-> "vstart"
mapping clause csr_name_map = 0x009  <-> "vxsat"
mapping clause csr_name_map = 0x00A  <-> "vxrm"
mapping clause csr_name_map = 0x00F  <-> "vcsr"
mapping clause csr_name_map = 0xC20  <-> "vl"
mapping clause csr_name_map = 0xC21  <-> "vtype"
mapping clause csr_name_map = 0xC22  <-> "vlenb"

val csr_name : csreg -> string
overload to_str = {csr_name}

/* Extensions may want to add additional CSR registers to the CSR address map.
 * These scattered functions support access to such registers.
 *
 * The default implementation provides access to the CSRs added by the 'N'
 * extension.
 */


/* returns whether a CSR is defined and accessible at a given address
 * and privilege
 */
val ext_is_CSR_defined : (csreg, Privilege) -> bool
scattered function ext_is_CSR_defined

/* returns the value of the CSR if it is defined */
val ext_read_CSR : csreg -> option(xlenbits)
scattered function ext_read_CSR

/* returns new value (after legalisation) if the CSR is defined */
val ext_write_CSR : (csreg, xlenbits) -> option(xlenbits)
scattered function ext_write_CSR
