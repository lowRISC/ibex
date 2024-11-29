

#include "svdpi.h"
/** it should have a dedicade header file */


#define STRINGIFY(x) #x
#define TOSTRING(x) STRINGIFY(x)

// Concatenate macros
#define CONCATENATE(a, b) a##b
#define CONCATENATE2(a, b) CONCATENATE(a, b)

#ifndef TOPLEVEL_NAME
#error "TOPLEVEL_NAME must be set to the name of the toplevel."
#else
#pragma message ("TOPLEVEL_NAME is set to: " TOSTRING(TOPLEVEL_NAME))
#endif

// Construct the include _Dpi.h file name
#define TOP_LEVEL_DPI_HEADER_NAME CONCATENATE2(V, TOPLEVEL_NAME)__Dpi.h

// Construct the include top module file name
#define TOP_LEVEL_HEADER_NAME CONCATENATE2(V, TOPLEVEL_NAME).h

#define TOP_LEVEL_DUT CONCATENATE2(V, TOPLEVEL_NAME)

//#include TOSTRING(TOP_LEVEL_DPI_HEADER_NAME)
#include TOSTRING(TOP_LEVEL_HEADER_NAME)


/**header file ends here */

#include "verilated_vcd_c.h"
#include "verilated.h"

#include <iostream>
#include <iomanip>
#include <fstream>
#include <exception>
#include <cstdio>
#include <cstdint>
#include <cerrno>




typedef TOP_LEVEL_DUT VTopModule;
typedef std::unique_ptr<VTopModule> dut_ptr;

void dut_reset(dut_ptr&dut, const vluint64_t sim_time, const vluint64_t rst_time, const vluint64_t rst_cycles) {
  dut->rst_ni = 0;
  if (sim_time > rst_time && sim_time < rst_time + rst_cycles) dut->rst_ni = 1;

  if (sim_time > rst_time + rst_cycles && sim_time < rst_time + 2 * rst_cycles) dut->rst_ni = 0;

  if (sim_time > rst_time + 2 * rst_cycles) dut->rst_ni = 1;
}

void dut_set_fetch_en(dut_ptr&dut, const vluint64_t sim_time, bool value) {
  dut->fetch_enable_i = 0;
  if (sim_time > 100) {
    dut->fetch_enable_i = value;
  }
}

int main(int argc, char **argv, char **env){

    uint32_t timeOut{207374};
    Verilated::commandArgs(argc, argv);
    dut_ptr dut = std::make_unique<VTopModule>();

    Verilated::traceEverOn(true);
    auto tfp = std::make_unique<VerilatedVcdC>();
  dut->trace(tfp.get(), 5);
    tfp->open("verilator_tb.vcd");
//https://github.com/verilator/verilator/blob/v5.028/include/verilated.h
  VerilatedContext* contextp = dut->contextp();
  while (!Verilated::gotFinish()  && (contextp->time()< timeOut) ) {
        // Start clock toggling
    dut->clk_i ^= 1;

    // Reset DUT
    dut_reset(dut, contextp->time(), 20, 10);
    // Set fetch enable to core
    dut_set_fetch_en(dut, contextp->time(), 1);
    dut->eval();
    tfp->dump(contextp->time());
    contextp->timeInc(1);
  }

  dut->final();
  tfp->close();
  //delete dut;
  exit(EXIT_SUCCESS);
    }
