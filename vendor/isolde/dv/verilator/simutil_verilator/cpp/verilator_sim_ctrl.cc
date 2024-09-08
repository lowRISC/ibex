// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilator_sim_ctrl.h"

#include <getopt.h>
#include <signal.h>
#include <sys/stat.h>
#include <verilated.h>

#include <iostream>

VerilatorSimCtrl &VerilatorSimCtrl::GetInstance() {
  static VerilatorSimCtrl instance;
  return instance;
}

bool VerilatorSimCtrl::ParseCommandArgs(int argc, char **argv, bool &exit_app) {
  contextp->commandArgs(argc, argv);
  exit_app = false;
    // Parse arguments for all registered extensions
  for (auto it = extension_array_.begin(); it != extension_array_.end(); ++it) {
    if (!(*it)->ParseCLIArguments(argc, argv, exit_app)) {
      exit_app = true;
      return false;
      if (exit_app) {
        return true;
      }
    }
  }
  return true;
}

void VerilatorSimCtrl::RunSimulation() {
  // Run the simulation
  Run();
  // Print simulation speed info
  PrintStatistics();
  // Print helper message for tracing
  {
    std::cout << std::endl
              << "You can view the simulation traces by calling" << std::endl
              << "$ gtkwave " << GetTraceFileName() << std::endl;
  }
}

void VerilatorSimCtrl::SetInitialResetDelay(unsigned int cycles) {
  initial_reset_delay_cycles_ = cycles;
}

void VerilatorSimCtrl::SetResetDuration(unsigned int cycles) {
  reset_duration_cycles_ = cycles;
}

void VerilatorSimCtrl::SetTimeout(unsigned int cycles) {
  term_after_cycles_ = cycles;
}

void VerilatorSimCtrl::RequestStop(bool simulation_success) {
  request_stop_ = true;
  simulation_success_ &= simulation_success;
}

void VerilatorSimCtrl::RegisterExtension(SimCtrlExtension *ext) {
  extension_array_.push_back(ext);
}

VerilatorSimCtrl::VerilatorSimCtrl()
    : contextp{new VerilatedContext},
      top_{new VERILATED_TOPLEVEL_NAME{contextp.get(), "TOP"}},
      time_(0),
      trace_file_dir_("logs"),
      initial_reset_delay_cycles_(2),
      reset_duration_cycles_(2),
      request_stop_(false),
      simulation_success_(true),
      term_after_cycles_(0) {
  // Create logs/ directory in case we have traces to put under it
  Verilated::mkdir("logs");
  // Set debug level, 0 is off, 9 is highest presently used
  // May be overridden by commandArgs argument parsing
  contextp->debug(0);

  // Randomization reset policy
  // May be overridden by commandArgs argument parsing
  contextp->randReset(2);

  // Verilator must compute traced signals
  contextp->traceEverOn(true);
}

void VerilatorSimCtrl::PrintHelp() const {
  std::cout << "Execute a simulation model for " << GetName() << "\n\n";

  std::cout << "-c|--term-after-cycles=N\n"
               "  Terminate simulation after N cycles. 0 means no timeout.\n\n"
               "-h|--help\n"
               "  Show help\n\n"
               "All arguments are passed to the design and can be used "
               "in the design, e.g. by DPI modules.\n\n";
}

void VerilatorSimCtrl::PrintStatistics() const {
  double speed_hz = time_ / 2 / (GetExecutionTimeMs() / 1000.0);
  double speed_khz = speed_hz / 1000.0;

  std::cout << std::endl
            << "Simulation statistics" << std::endl
            << "=====================" << std::endl
            << "Executed cycles:  " << std::dec << time_ / 2 << std::endl
            << "Wallclock time:   " << GetExecutionTimeMs() / 1000.0 << " s"
            << std::endl
            << "Simulation speed: " << speed_hz << " cycles/s " << "("
            << speed_khz << " kHz)" << std::endl;

  int trace_size_byte;
  if ( FileSize(GetTraceFileName(), trace_size_byte)) {
    std::cout << "Trace file size:  " << trace_size_byte << " B" << std::endl;
  }
}

std::string VerilatorSimCtrl::GetTraceFileName() const {
  return trace_file_dir_+std::string("/ibex.vcd");
}

void VerilatorSimCtrl::Run() {

  
    auto tfp = std::make_unique<VerilatedVcdC>();
    // Verilator must compute traced signals
    contextp->traceEverOn(true);
    top_->trace(tfp.get(), 99);  // Trace 99 levels of hierarchy
    Verilated::mkdir(trace_file_dir_.c_str());
    tfp->open(GetTraceFileName().c_str());
  



  std::cout << std::endl
            << "Simulation running, end by pressing CTRL-c." << std::endl;

  time_begin_ = std::chrono::steady_clock::now();
  AssertReset();
  top_->CLK_I = 0;
  // Evaluate all initial blocks, including the DPI setup routines
  //top_->eval();
  unsigned long start_reset_cycle_ = initial_reset_delay_cycles_;
  unsigned long end_reset_cycle_ = start_reset_cycle_ + reset_duration_cycles_;
  contextp->time(0);
  while (1) {
   
    unsigned long cycle_ = time_ / 2;


    if (cycle_ == start_reset_cycle_) {
      AssertReset();
    } else if (cycle_ == end_reset_cycle_) {
      DeassertReset();
    }


    top_->CLK_I = !top_->CLK_I;


    top_->eval();
    tfp->dump(time_);
    contextp->timeInc(1); // 1 timeprecision period passes...
    time_++;


    if (request_stop_) {
      std::cout << "Received stop request, shutting down simulation."
                << std::endl;
      break;
    }
    if (contextp->gotFinish()) {
      std::cout << "Received $finish() from Verilog, shutting down simulation."
                << std::endl;
      break;
    }
    if (term_after_cycles_ && (time_ / 2 >= term_after_cycles_)) {
      std::cout << "Simulation timeout of " << term_after_cycles_
                << " cycles reached, shutting down simulation." << std::endl;
      break;
    }
  }
 time_end_ = std::chrono::steady_clock::now();
  // Final model cleanup
  top_->final();
  tfp->close();
    // Final simulation summary
  contextp->statsPrintSummary();
}

std::string VerilatorSimCtrl::GetName() const {
  if (top_) {
    return top_->name();
  }
  return "unknown";
}

unsigned int VerilatorSimCtrl::GetExecutionTimeMs() const {
  return std::chrono::duration_cast<std::chrono::milliseconds>(time_end_ -
                                                               time_begin_)
      .count();
}

void VerilatorSimCtrl::AssertReset() {
  //if (flags_ & ResetPolarityNegative) {
    top_->RST_NI = 0;
 // } else {
 //   top->RST_NI = 1;
 // }
}

void VerilatorSimCtrl::DeassertReset() {
  //if (flags_ & ResetPolarityNegative) {
    top_->RST_NI = 1;
//  } else {
 //   top->RST_NI = 0;
//  }
}

bool VerilatorSimCtrl::FileSize(std::string filepath, int &size_byte) const {
  struct stat statbuf;
  if (stat(filepath.data(), &statbuf) != 0) {
    size_byte = 0;
    return false;
  }

  size_byte = statbuf.st_size;
  return true;
}
