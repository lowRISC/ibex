// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef ISOLDE_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATED_TOPLEVEL_H_
#define ISOLDE_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATED_TOPLEVEL_H_

#ifndef TOPLEVEL_NAME
#error "TOPLEVEL_NAME must be set to the name of the toplevel."
#endif

#include <verilated.h>

#define STR(s) #s
#define STR_AND_EXPAND(s) STR(s)

// Include Verilator-generated toplevel
#define VERILATED_TOPLEVEL_HEADER_STR2(s) STR(V##s)
#define VERILATED_TOPLEVEL_HEADER_STR(s) VERILATED_TOPLEVEL_HEADER_STR2(s)

// Include model header, generated from Verilating "top.v"
#include VERILATED_TOPLEVEL_HEADER_STR(TOPLEVEL_NAME.h)

// Name of the Verilated class
#define VERILATED_TOPLEVEL_NAME3(s) V##s
#define VERILATED_TOPLEVEL_NAME2(s) VERILATED_TOPLEVEL_NAME3(s)
#define VERILATED_TOPLEVEL_NAME VERILATED_TOPLEVEL_NAME2(TOPLEVEL_NAME)


#include <verilated_vcd_c.h>


#endif  // ISOLDE_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATED_TOPLEVEL_H_
