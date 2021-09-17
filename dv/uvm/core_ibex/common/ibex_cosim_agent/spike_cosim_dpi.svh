// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import "DPI-C" function chandle spike_cosim_init(bit [31:0] start_pc, bit [31:0] start_mtvec,
  string log_file_path);
import "DPI-C" function void spike_cosim_release(chandle cosim_handle);
