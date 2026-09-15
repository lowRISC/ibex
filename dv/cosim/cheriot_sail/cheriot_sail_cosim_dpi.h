// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef CHERIOT_SAIL_COSIM_DPI_H_
#define CHERIOT_SAIL_COSIM_DPI_H_

#include <stdint.h>

// svBitVecVal = uint32_t, svBit = unsigned char (IEEE 1800 / svdpi.h).
// Defined here so this header can be used without Xcelium headers.
#ifndef SV_PACKED_DATA_NEDTYPES
#define SV_PACKED_DATA_NEDTYPES
typedef uint32_t      svBitVecVal;
typedef unsigned char svBit;
#endif

#ifdef __cplusplus
extern "C" {
#endif

// Initialize the cheriot-sail model. Must be called once before any step().
// boot_addr: reset PC and mtvec (matches CHERIoT-Ibex boot_addr_i).
// bit[31:0] → const svBitVecVal * (Xcelium DPI convention for packed vectors)
void cheriot_sail_cosim_init(const svBitVecVal *boot_addr);

// Advance the model by one retired instruction and compare CHERI outputs.
//
// insn:        32-bit instruction word (from RTL RVFI rvfi_insn)
// pc:          program counter of this instruction (rvfi_pc_rdata)
// cheri_rf_we: 1 if the instruction wrote a capability register  (bit → svBit)
// cheri_rd:    5-bit destination capability register address     (bit[4:0] → svBitVecVal*)
// cheri_rtag:  tag bit written to the capability register        (bit → svBit)
//
// Returns 0 on match, -1 if the model disagrees (errors queued via
// cheriot_sail_cosim_get_error).
int cheriot_sail_cosim_step(const svBitVecVal *insn,
                             const svBitVecVal *pc,
                             svBit cheri_rf_we,
                             const svBitVecVal *cheri_rd,
                             svBit cheri_rtag);

// Tear down the model (frees Sail runtime state). Safe to call on cleanup and
// before re-initializing after a reset.
void cheriot_sail_cosim_cleanup(void);

// Return the Sail model's mtval value after the last step() (valid when that step was a trap).
uint32_t    cheriot_sail_cosim_get_mtval(void);

// Error reporting — same pattern as riscv_cosim_get_error.
int         cheriot_sail_cosim_get_num_errors(void);
const char *cheriot_sail_cosim_get_error(int index);
void        cheriot_sail_cosim_clear_errors(void);

// Backdoor memory initialisation: write one byte into the Sail model's RAM.
// Call after cheriot_sail_cosim_init(), before the first step().
void cheriot_sail_cosim_write_mem_byte(const svBitVecVal *addr,
                                       svBit data);

#ifdef __cplusplus
}
#endif

#endif  // CHERIOT_SAIL_COSIM_DPI_H_
