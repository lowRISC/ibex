// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Binds formal_tb into ibex_branch_predict so the testbench assertions
// can reference the DUT's ports directly via wildcard connections.
bind ibex_branch_predict formal_tb bp_tb_i (.*);
