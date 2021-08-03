// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <string>
#include <vector>

#ifndef COSIM_H_
#define COSIM_H_

class Cosim {
 public:
  virtual ~Cosim() {}
  // Add a memory to the co-simulator environment. Use
  // `backdoor_write_mem`/`backdoor_read_mem` to access it from the simulation
  // environment.
  virtual void add_memory(uint32_t base_addr, size_t size) = 0;

  // Write bytes to co-simulator memory
  //
  // returns false if write fails (e.g. because no memory exists at the bytes
  // being written).
  virtual bool backdoor_write_mem(uint32_t addr, size_t len,
                                  const uint8_t *data_in) = 0;

  // Read bytes from co-simulator memory
  //
  // returns false if read fails (e.g. because no memory exists at the bytes
  // being read).
  virtual bool backdoor_read_mem(uint32_t addr, size_t len,
                                 uint8_t *data_out) = 0;

  // Step the co-simulator, checking register write and PC of executed
  // instruction match the supplied values. A write_reg of 0 indicates no
  // register write occurred.
  //
  // Returns false if there is a mismatch, use `get_errors` to obtain details
  virtual bool step(uint32_t write_reg, uint32_t write_reg_data,
      uint32_t pc) = 0;

  // Set the value of MIP
  //
  // At the next call of `step`, the MIP value will take effect (i.e. if it's a
  // new interrupt that is enabled it will step straight to that handler).
  virtual void set_mip(uint32_t mip) = 0;

  // Set the debug request
  //
  // When set to true the core will enter debug mode at the next step
  virtual void set_debug_req(bool debug_req) = 0;

  // Get a vector of strings describing errors that have occurred during `step`
  virtual const std::vector<std::string> &get_errors() = 0;

  // Clear internal vector of error descriptions
  virtual void clear_errors() = 0;
};

#endif //COSIM_H_
