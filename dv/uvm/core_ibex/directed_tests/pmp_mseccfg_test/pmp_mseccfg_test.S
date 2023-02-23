# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

###############################################################################
# Description:
#   Setting mseccfg.mml 1 and mseccfg.rlb 0/1 with different PMP.LXWR 
# permissions and check R/w access to that specific region. Access is
# at start, mid and end of the PMP region.
#   Target of test is to achieve functional coverage for rewriting 
# permissions in PMP regions with RLB 0/1.

#include "riscv_test.h"
#include "test_macros.h"
#include "custom_macros.h"

#define PMP_GRAN 0x1000

#if SET_PMP_L == 1
  #define SET_PMP_L_BIT PMP_L
#else
  #define SET_PMP_L_BIT 0
#endif

#if SET_PMP_L_PREV == 1
  #define SET_PMP_L_PREV PMP_L
#else
  #define SET_PMP_L_PREV 0
#endif

# Test specific macros
#define SET_PMP_AND_ACCESS_TOR(pmp_permissions, region_high, region_low)                            \
  SET_PMP_TOR(pmp_region_end, pmp_region_start, pmp_permissions | PMP_TOR, region_high, region_low) \
  RW_ACCESSES(pmp_region_start, PMP_GRAN)

#define SET_PMP_AND_ACCESS_NAPOT(pmp_permissions, region)                        \
  SET_PMP_NAPOT(pmp_region_start, PMP_GRAN, pmp_permissions | PMP_NAPOT, region) \
  RW_ACCESSES(pmp_region_start, PMP_GRAN)

#define SET_DIFF_PMP_CFG(pmp_region, pmp_l, pmp_l_prev)               \
  PREV_PMP_CFG(pmp_l_prev, pmp_region, pmp_l)                         \
  PREV_PMP_CFG(pmp_l_prev | PMP_R, pmp_region, pmp_l)                 \
  PREV_PMP_CFG(pmp_l_prev | PMP_W, pmp_region, pmp_l)                 \
  PREV_PMP_CFG(pmp_l_prev | PMP_X, pmp_region, pmp_l)                 \
  PREV_PMP_CFG(pmp_l_prev | PMP_R | PMP_W, pmp_region, pmp_l)         \
  PREV_PMP_CFG(pmp_l_prev | PMP_R | PMP_X, pmp_region, pmp_l)         \
  PREV_PMP_CFG(pmp_l_prev | PMP_W | PMP_X, pmp_region, pmp_l)         \
  PREV_PMP_CFG(pmp_l_prev | PMP_R | PMP_W | PMP_X, pmp_region, pmp_l)

#define PREV_PMP_CFG(prev_pmp, pmp_region, pmp_l)                    \
  SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                     \
  SET_PMP_AND_ACCESS_NAPOT(pmp_l, pmp_region)                        \
  SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                     \
  SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_R, pmp_region)                \
  SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                     \
  SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_W, pmp_region)                \
  SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                     \
  SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_X, pmp_region)                \
  SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                     \
  SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_R | PMP_W, pmp_region)        \
  SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                     \
  SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_R | PMP_X, pmp_region)        \
  SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                     \
  SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_W | PMP_X, pmp_region)        \
  SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                     \
  SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_R | PMP_W | PMP_X, pmp_region)

#ifdef PMP_NEXT_L1
  #define PREV_PMP_CFG_UNIQUE(prev_pmp, pmp_region, pmp_l)           \
    SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                   \
    SET_PMP_AND_ACCESS_NAPOT(pmp_l, pmp_region)
#endif

#ifdef PMP_NEXT_L1_R1
  #define PREV_PMP_CFG_UNIQUE(prev_pmp, pmp_region, pmp_l)           \
    SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                   \
    SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_R, pmp_region)
#endif

#ifdef PMP_NEXT_L1_W1
  #define PREV_PMP_CFG_UNIQUE(prev_pmp, pmp_region, pmp_l)           \
    SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                   \
    SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_W, pmp_region)
#endif

#ifdef PMP_NEXT_L1_X1
  #define PREV_PMP_CFG_UNIQUE(prev_pmp, pmp_region, pmp_l)           \
    SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                   \
    SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_X, pmp_region)
#endif

#ifdef PMP_NEXT_L1_R1_W1
  #define PREV_PMP_CFG_UNIQUE(prev_pmp, pmp_region, pmp_l)           \
    SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                   \
    SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_R | PMP_W, pmp_region)
#endif

#ifdef PMP_NEXT_L1_R1_X1
  #define PREV_PMP_CFG_UNIQUE(prev_pmp, pmp_region, pmp_l)           \
    SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                   \
    SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_R | PMP_X, pmp_region)
#endif

#ifdef PMP_NEXT_L1_W1_X1
  #define PREV_PMP_CFG_UNIQUE(prev_pmp, pmp_region, pmp_l)           \
    SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                   \
    SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_W | PMP_X, pmp_region)
#endif

#ifdef PMP_NEXT_L1_R1_W1_X1
  #define PREV_PMP_CFG_UNIQUE(prev_pmp, pmp_region, pmp_l)           \
    SET_PMP_AND_ACCESS_NAPOT(prev_pmp, pmp_region)                   \
    SET_PMP_AND_ACCESS_NAPOT(pmp_l | PMP_R | PMP_W | PMP_X, pmp_region)
#endif

RVTEST_RV64M
RVTEST_CODE_BEGIN

  # setting machine handler
  la   t0, mtvec_handler
  csrw mtvec, t0

  # resetting all PMP regions and mseccfg
  RESET_PMP

#ifdef RLB
  SET_MSECCFG(MSECCFG_RLB)
#endif

  # setting M mode permissions as unmatched regions would be ignored when mml 1
  SET_PMP_TOR(pmp_region_start, _start, PMP_L | PMP_R | PMP_X | PMP_TOR, 0, 0)

  # MML 1
  SET_MSECCFG(MSECCFG_MML)

  # If RLB 1, PMP locked regions would be modifiable
#ifdef RLB
  SET_DIFF_PMP_CFG(PMP_REGION, SET_PMP_L_BIT, SET_PMP_L_PREV)
#else
  #if SET_PMP_L == 1
    # If RLB 0, then once locked, not modifiable hence have to use
    # different PMP regions to cover all transitions
    PREV_PMP_CFG_UNIQUE(SET_PMP_L_PREV, 4, SET_PMP_L_BIT)
    PREV_PMP_CFG_UNIQUE(SET_PMP_L_PREV | PMP_R, 5, SET_PMP_L_BIT)
    PREV_PMP_CFG_UNIQUE(SET_PMP_L_PREV | PMP_W, 6, SET_PMP_L_BIT)
    PREV_PMP_CFG_UNIQUE(SET_PMP_L_PREV | PMP_X, 7, SET_PMP_L_BIT)
    PREV_PMP_CFG_UNIQUE(SET_PMP_L_PREV | PMP_R | PMP_W, 8, SET_PMP_L_BIT)
    PREV_PMP_CFG_UNIQUE(SET_PMP_L_PREV | PMP_R | PMP_X, 9, SET_PMP_L_BIT)
    PREV_PMP_CFG_UNIQUE(SET_PMP_L_PREV | PMP_W | PMP_X, 10, SET_PMP_L_BIT)
    PREV_PMP_CFG_UNIQUE(SET_PMP_L_PREV | PMP_R | PMP_W | PMP_X, 11, SET_PMP_L_BIT)
  #else
    # If not locked, PMPCFG would be writable
    SET_DIFF_PMP_CFG(PMP_REGION, SET_PMP_L_BIT, SET_PMP_L_PREV)
  #endif
#endif

  j pass

  TEST_PASSFAIL

.balign 256
mtvec_handler:
  SKIP_PC
  mret

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

.balign PMP_GRAN
pmp_region_start: .zero PMP_GRAN
pmp_region_end:
  TEST_DATA

RVTEST_DATA_END
