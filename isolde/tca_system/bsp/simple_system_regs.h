// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef SIMPLE_SYSTEM_REGS_H__
#define SIMPLE_SYSTEM_REGS_H__
/**
see tb/core/mm_ram.sv
    localparam int                        MMADDR_TESTSTATUS = 32'h2000_0000;
    localparam int                        MMADDR_EXIT       = 32'h2000_0004;
*/


#define MMADDR_EXIT                0x80000000
#define MMADDR_PRINT               0x80000004
#define MMADDR_CYCLE_COUNTER       MMADDR_EXIT

//#define SIM_CTRL_BASE 0x20000
//#define SIM_CTRL_OUT 0x0
//#define SIM_CTRL_CTRL 0x8

// #define TIMER_BASE 0x30000
// #define TIMER_MTIME 0x0
// #define TIMER_MTIMEH 0x4
// #define TIMER_MTIMECMP 0x8
// #define TIMER_MTIMECMPH 0xC



#endif  // SIMPLE_SYSTEM_REGS_H__
