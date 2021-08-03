// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef COSIM_DPI_H_
#define COSIM_DPI_H_

#include <stdint.h>
#include <svdpi.h>

// This adapts the C++ interface of the `Cosim` class to be used via DPI. See
// the documentation in cosim.h for further details

extern "C" {
int riscv_cosim_step(void *cosim_handle, const svBitVecVal *write_reg,
                     const svBitVecVal *write_reg_data, const svBitVecVal *pc);
void riscv_cosim_set_mip(void *cosim_handle, const svBitVecVal *mip);
void riscv_cosim_set_debug_req(void *cosim_handle, svBit debug_req);
int riscv_cosim_get_num_errs(void *cosim_handle);
const char *riscv_cosim_get_err(void *cosim_handle, int index);
void riscv_cosim_clear_errs(void *cosim_handle);
}

#endif // COSIM_DPI_H_
