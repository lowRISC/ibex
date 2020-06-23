// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to probe the instruction moving through the pipeline
//
// TODO: does not support dummy instruction insertion right now,
//       might have to revisit and update.
interface core_ibex_instr_monitor_if #(parameter DATA_WIDTH = 32);

  // ID stage
  logic                   valid_id;
  logic                   err_id;
  logic                   is_compressed_id;
  logic [15:0]            instr_compressed_id;
  logic [DATA_WIDTH-1:0]  instr_id;

endinterface
