// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface ibex_icache_if (input clk);

  // Set when core is enabled (and might request instructions soon)
  logic         req;

  // Branch request
  logic         branch;
  logic [31:0]  branch_addr;

  // Passing instructions back to the core
  logic         ready;
  logic         valid;
  logic [31:0]  rdata;
  logic [31:0]  addr;
  logic         err;
  logic         err_plus2;

  // Enable/disable or invalidate the cache
  logic         enable;
  logic         invalidate;

  // Busy signal from the cache (either there's a request on the bus or the cache is invalidating
  // itself)
  logic         busy;

  // Drive the branch pin for a single cycle, redirecting the cache to the given instruction
  // address.
  task automatic branch_to(logic [31:0] addr);
    branch      <= 1'b1;
    branch_addr <= addr;

    @(posedge clk);

    branch      <= 1'b0;
    branch_addr <= 'X;
  endtask

  // Raise a pulse on the invalidate line for the given number of cycles.
  //
  // A one-cycle pulse will start an invalidation, but testing might want a longer pulse (which the
  // cache should support)
  task automatic invalidate_pulse(int num_cycles);
    invalidate <= 1'b1;
    repeat (num_cycles) @(posedge clk);
    invalidate <= 1'b0;
  endtask

  // A task that waits for num_clks posedges on the clk signal
  task automatic wait_clks(int num_clks);
    repeat (num_clks) @(posedge clk);
  endtask

  // Reset all the signals from the core to the cache (the other direction is controlled by the
  // DUT)
  task automatic reset();
    req        <= 1'b0;
    branch     <= 1'b0;
    ready      <= 1'b0;
    enable     <= 1'b0;
    invalidate <= 1'b0;
  endtask

endinterface
