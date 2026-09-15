// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// DPI imports for the cheriot-sail cosim oracle.
// Include this file in any SV module that calls into the Sail model.

`ifndef CHERIOT_SAIL_COSIM_DPI_SVH
`define CHERIOT_SAIL_COSIM_DPI_SVH

// Initialize (or re-initialize after reset) the Sail model.
// boot_addr: reset PC and mtvec (match CHERIoT-Ibex boot_addr_i).
import "DPI-C" function void cheriot_sail_cosim_init(bit [31:0] boot_addr);

// Tear down the model and release Sail runtime state.
import "DPI-C" function void cheriot_sail_cosim_cleanup();

// Advance the model by one retired CHERIoT instruction and compare outputs.
//
// insn:        32-bit instruction word (RVFI rvfi_insn)
// pc:          instruction PC (rvfi_pc_rdata)
// cheri_rf_we: 1 if instruction wrote a capability register
// cheri_rd:    5-bit destination capability register address
// cheri_rtag:  tag bit written to the capability register by the RTL
//
// Returns 0 on match, -1 on mismatch (errors queued in the model).
import "DPI-C" function int cheriot_sail_cosim_step(
  bit [31:0] insn,
  bit [31:0] pc,
  bit        cheri_rf_we,
  bit [ 4:0] cheri_rd,
  bit        cheri_rtag
);

// Return the Sail model's mtval register after the last step (valid when that step was a trap).
import "DPI-C" function bit [31:0] cheriot_sail_cosim_get_mtval();

// Error reporting.
import "DPI-C" function int  cheriot_sail_cosim_get_num_errors();
import "DPI-C" function string cheriot_sail_cosim_get_error(int index);
import "DPI-C" function void cheriot_sail_cosim_clear_errors();

// Backdoor memory load: write one byte into the Sail model's RAM.
// Call after cheriot_sail_cosim_init(), before the first step().
import "DPI-C" function void cheriot_sail_cosim_write_mem_byte(
  bit [31:0] addr,
  bit [ 7:0] data
);

`endif  // CHERIOT_SAIL_COSIM_DPI_SVH
