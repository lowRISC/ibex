// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdlib.h>
#include <iostream>
#include <utility>
#include <string>
#include "Vibex_tracing_tb.h"
#include "verilated_vcd_c.h"

vluint64_t sim_time = 0;

// This function is needed to ensure verilator
// knows the current simulation time
double sc_time_stamp () {
  return sim_time;
}

int main(int argc, char **argv) {
  Verilated::commandArgs(argc, argv);
  Verilated::traceEverOn(true);

  Vibex_tracing_tb *top = new Vibex_tracing_tb;
  VerilatedVcdC* tfp = new VerilatedVcdC;

  top->trace (tfp, 99);
  tfp->open ("ibex_trace.vcd");

  top->clk   = 0;
  top->rst_n = 0;

  while (!Verilated::gotFinish()) {
    if (sim_time == 160) {
      top->rst_n = 1;
    } else if (sim_time == 200) {
      top->instr_rdata  = 0x81868106;
      top->instr_rvalid = 0;
      top->instr_gnt    = 1;
    } else if (sim_time == 210) {
      top->instr_rvalid = 1;
      top->instr_gnt    = 0;
    } else if (sim_time == 220) {
      top->instr_rvalid = 0;
    } else if (sim_time == 250) {
      top->instr_rdata  = 0x00400113;
      top->instr_rvalid = 0;
      top->instr_gnt    = 1;
    } else if (sim_time == 260) {
      top->instr_rvalid = 1;
      top->instr_gnt    = 0;
    } else if (sim_time == 270) {
      top->instr_rvalid = 0;
      top->instr_rdata  = 0xff810113;
      top->instr_gnt    = 1;
    } else if (sim_time == 280) {
      top->instr_rvalid = 1;
      top->instr_gnt    = 0;
    } else if (sim_time == 290) {
      top->instr_rvalid = 0;
      top->instr_rdata  = 0x4000006f;
      top->instr_gnt    = 1;
    } else if (sim_time == 300) {
      top->instr_rvalid = 1;
      top->instr_gnt    = 0;
    } else if (sim_time == 310) {
      top->instr_rvalid = 0;
    } else if (sim_time == 320) {
      top->instr_rdata  = 0x039597b3;
      top->instr_gnt    = 1;
    } else if (sim_time == 330) {
      top->instr_rvalid = 1;
      top->instr_gnt    = 1;
    } else if (sim_time == 340) {
      top->instr_rdata  = 0x13410d13;
    } else if (sim_time == 350) {
      top->instr_rdata  = 0xe1070713;
    } else if (sim_time == 360) {
      top->instr_rdata  = 0xfff7c793;
    } else if (sim_time == 370) {
      top->instr_rdata  = 0x00000013;
    } else if (sim_time == 380) {
      top->instr_rdata  = 0x002d2c23;
    } else if (sim_time == 390) {
      top->instr_rdata  = 0x00000013;
    } else if (sim_time == 400) {
      top->instr_rdata  = 0x000d2083;
      top->data_rdata   = 0x12345678;
    } else if (sim_time == 410) {
      top->instr_rdata  = 0x60008113;
    } else if (sim_time == 420) {
      top->instr_rdata  = 0x00000013;
    } else if (sim_time == 430) {
      top->instr_rdata  = 0x002d2023;
    } else if (sim_time == 450) {
      top->instr_rdata  = 0x0000000f;
    } else if (sim_time == 460) {
      top->instr_rdata  = 0x00000113;
    } else if (sim_time == 490) {
      top->instr_rdata  = 0x00000013;
    } else if (sim_time == 500) {
      top->instr_rdata  = 0x0000000f;
    }
    if (sim_time == 560) {
      top->sim_done = 1;
    }
    top->clk = !top->clk;
    top->eval();
    tfp->dump (sim_time);
    sim_time += 5;
  }
  tfp->close();
  delete top;
  exit(0);
}
