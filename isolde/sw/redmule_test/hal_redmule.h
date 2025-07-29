// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Yvan Tortorella <yvan.tortorella@unibo.it>
//

#ifndef __HAL_REDMULE_H__
#define __HAL_REDMULE_H__

#include "tensor_dim.h"

/* LOW-LEVEL HAL */
#define REDMULE_ADDR_BASE REDMULE_BASE_ADD
#define REDMULE_ADDR_SPACE 0x00000100

#define HWPE_WRITE(value, offset) *(int *)(REDMULE_ADDR_BASE + offset) = value
#define HWPE_READ(offset) *(int *)(REDMULE_ADDR_BASE + offset)

static inline void redmule_x_add_set(unsigned int value) {
  HWPE_WRITE(value, REDMULE_REG_OFFS + REDMULE_REG_X_PTR);
}

static inline void redmule_w_add_set(unsigned int value) {
  HWPE_WRITE(value, REDMULE_REG_OFFS + REDMULE_REG_W_PTR);
}

static inline void redmule_z_add_set(unsigned int value) {
  HWPE_WRITE(value, REDMULE_REG_OFFS + REDMULE_REG_Z_PTR);
}

static inline void redmule_mcfg_set(uint32_t mcfg0, uint32_t mcfg1) {
  HWPE_WRITE(mcfg0, REDMULE_REG_OFFS + REDMULE_MCFG0_PTR);
  HWPE_WRITE(mcfg1, REDMULE_REG_OFFS + REDMULE_MCFG1_PTR);
}

static inline void redmule_arith_set(uint32_t arith) {
  HWPE_WRITE(arith, REDMULE_REG_OFFS + REDMULE_ARITH_PTR);
}

static inline void hwpe_trigger_job() { HWPE_WRITE(0, REDMULE_TRIGGER); }

static inline int hwpe_acquire_job() { return HWPE_READ(REDMULE_ACQUIRE); }

static inline unsigned int hwpe_get_status() { return HWPE_READ(REDMULE_STATUS); }

static inline void hwpe_soft_clear() {
  HWPE_WRITE(0, REDMULE_SOFT_CLEAR);
}

static inline void hwpe_cg_enable() { return; }

static inline void hwpe_cg_disable() { return; }

void redmule_cfg(unsigned int x, unsigned int w, unsigned int z, uint16_t m_size, uint16_t n_size,
                 uint16_t k_size, uint8_t gemm_op, uint8_t gemm_fmt) {

  uint32_t mcfg_reg0 = 0;
  uint32_t mcfg_reg1 = 0;
  uint32_t arith_reg = 0;

  mcfg_reg0 = (k_size << 16) | (m_size << 0);
  mcfg_reg1 = n_size << 0;

  arith_reg = (gemm_op << 10) | (gemm_fmt << 7);

  redmule_x_add_set((unsigned int)x);
  redmule_w_add_set((unsigned int)w);
  redmule_z_add_set((unsigned int)z);
  redmule_mcfg_set((unsigned int)mcfg_reg0, (unsigned int)mcfg_reg1);
  redmule_arith_set((unsigned int)arith_reg);
}

#endif
