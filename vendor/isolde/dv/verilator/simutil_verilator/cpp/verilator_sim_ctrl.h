// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef ISOLDE_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATOR_SIM_CTRL_H_
#define ISOLDE_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATOR_SIM_CTRL_H_

#include <chrono>
#include <string>
#include <vector>

// For std::unique_ptr
#include <memory>
#include "sim_ctrl_extension.h"
#include "verilated_toplevel.h"

enum VerilatorSimCtrlFlags {
  Defaults = 0,
  ResetPolarityNegative = 1,
};

/**
 * Simulation controller for verilated simulations
 */
class VerilatorSimCtrl {
 public:
  /**
   * Get the simulation controller instance
   *
   * @see SetTop()
   */
  static VerilatorSimCtrl &GetInstance();

  VerilatorSimCtrl(VerilatorSimCtrl const &) = delete;
  void operator=(VerilatorSimCtrl const &) = delete;



  /**
   * Parse command line arguments
   *
   * Process all recognized command-line arguments from argc/argv. If a command
   * line argument implies that we should exit immediately (like --help), sets
   * exit_app. On failure, sets exit_app as well as returning false.
   *
   * @param argc, argv Standard C command line arguments
   * @param exit_app Indicate that program should terminate
   * @return Return code, true == success
   */
  bool ParseCommandArgs(int argc, char **argv, bool &exit_app);

  /**
   * A helper function to execute a standard set of run commands.
   *
   * This function performs the following tasks:
   * 1. Sets up a signal handler to enable tracing to be turned on/off during
   *    a run by sending SIGUSR1 to the process
   * 2. Prints some tracer-related helper messages
   * 3. Runs the simulation
   * 4. Prints some further helper messages and statistics once the simulation
   *    has run to completion
   */
  void RunSimulation();

  /**
   * Get the simulation result
   */
  bool WasSimulationSuccessful() const { return simulation_success_; }

  /**
   * Set the number of clock cycles (periods) before the reset signal is
   * activated
   */
  void SetInitialResetDelay(unsigned int cycles);

  /**
   * Set the number of clock cycles (periods) the reset signal is activated
   */
  void SetResetDuration(unsigned int cycles);

  /**
   * Set a timeout in clock cycles.
   *
   * This can be overridden by the user (in either direction) with the
   * --term-after-cycles command-line argument. Setting to zero means
   * no timeout, which is the default behaviour.
   */
  void SetTimeout(unsigned int cycles);

  /**
   * Request the simulation to stop
   */
  void RequestStop(bool simulation_success);

  /**
   * Register an extension to be called automatically
   */
  void RegisterExtension(SimCtrlExtension *ext);



 private:
  const std::unique_ptr<VerilatedContext> contextp;
  std::unique_ptr<VERILATED_TOPLEVEL_NAME> top_;
  //CData *sig_clk_;
  //CData *sig_rst_;
  //VerilatorSimCtrlFlags flags_;
  unsigned long time_;
  std::string trace_file_dir_;
  unsigned int initial_reset_delay_cycles_;
  unsigned int reset_duration_cycles_;
  volatile unsigned int request_stop_;
  volatile bool simulation_success_;
  std::chrono::steady_clock::time_point time_begin_;
  std::chrono::steady_clock::time_point time_end_;
  unsigned long term_after_cycles_;
  std::vector<SimCtrlExtension *> extension_array_;

  /**
   * Default constructor
   *
   * Use GetInstance() instead.
   */
  VerilatorSimCtrl();

  /**
   * Register the signal handler
   */
  void RegisterSignalHandler();

  /**
   * Signal handler callback
   *
   * Use RegisterSignalHandler() to setup.
   */
  static void SignalHandler(int sig);

  /**
   * Print help how to use this tool
   */
  void PrintHelp() const;

  

  /**
   * Print statistics about the simulation run
   */
  void PrintStatistics() const;

  /**
   * Get the file name of the trace file
   */
  std::string GetTraceFileName() const;

  /**
   * Run the main loop of the simulation
   *
   * This function blocks until the simulation finishes.
   */
  void Run();

  /**
   * Get a name for this simulation
   *
   * This name is typically the name of the top-level.
   */
  std::string GetName() const;

  /**
   * Get the wallclock execution time in ms
   */
  unsigned int GetExecutionTimeMs() const;

  /**
   * Assert the reset signal
   */
  void AssertReset();

  /**
   * Deassert the reset signal
   */
  void DeassertReset();

  /**
   * Return the size of a file
   */
  bool FileSize(std::string filepath, int &size_byte) const;


};

#endif  // ISOLDE_HW_DV_VERILATOR_SIMUTIL_VERILATOR_CPP_VERILATOR_SIM_CTRL_H_
