// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface ibex_mem_intf#(
  parameter int ADDR_WIDTH = 32,
  parameter int DATA_WIDTH = 32
) (
  input clk
);

  wire                     reset;
  wire                     request;
  wire                     grant;
  wire  [ADDR_WIDTH-1:0]   addr;
  wire                     we;
  wire  [DATA_WIDTH/8-1:0] be;
  wire                     rvalid;
  wire  [DATA_WIDTH-1:0]   wdata;
  wire  [DATA_WIDTH-1:0]   rdata;
  wire                     error;

  clocking request_driver_cb @(posedge clk);
    input   reset;
    output  request;
    input   grant;
    output  addr;
    output  we;
    output  be;
    input   rvalid;
    output  wdata;
    input   rdata;
    input   error;
  endclocking

  clocking response_driver_cb @(posedge clk);
    input   reset;
    input   request;
    output  grant;
    input   addr;
    input   we;
    input   be;
    output  rvalid;
    input   wdata;
    output  rdata;
    output  error;
  endclocking

  clocking monitor_cb @(posedge clk);
    input reset;
    input request;
    input grant;
    input addr;
    input we;
    input be;
    input rvalid;
    input wdata;
    input rdata;
    input error;
  endclocking

  task automatic wait_clks(input int num);
    repeat (num) @(posedge clk);
  endtask

  task automatic wait_neg_clks(input int num);
    repeat (num) @(negedge clk);
  endtask

endinterface : ibex_mem_intf
