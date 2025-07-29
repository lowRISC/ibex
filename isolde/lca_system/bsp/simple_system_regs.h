// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SIMPLE_SYSTEM_REGS_H__
#define SIMPLE_SYSTEM_REGS_H__



#define MMADDR_EXIT                0x80000000
#define MMADDR_PRINT               0x80000004
#define MMADDR_CYCLE_COUNTER       MMADDR_EXIT
#define MMADDR_PERF_TTY            0x80000008
#define MMADDR_PERF_COUNTERS       0x8000000C
#define SPM_NARROW_ADDR            0x80001000
#define SPM_NARROW_SIZE            0x00001000;  //64kB                                   



#endif  // SIMPLE_SYSTEM_REGS_H__
