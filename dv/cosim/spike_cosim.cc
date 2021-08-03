// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "spike_cosim.h"
#include "config.h"
#include "decode.h"
#include "devices.h"
#include "log_file.h"
#include "processor.h"
#include "simif.h"

#include <cassert>
#include <sstream>

SpikeCosim::SpikeCosim() {
  log = std::make_unique<log_file_t>("spike_trace.log");

  processor = std::make_unique<processor_t>("RV32IMC", "MSU", DEFAULT_VARCH,
                                            this, 0, false, log->get());

  processor->set_debug(true);
  processor->get_state()->pc = 0x100080;
  processor->get_state()->mtvec = 0x100001;
  processor->enable_log_commits();
}

// always return nullptr so all memory accesses go via mmio_load/mmio_store
char *SpikeCosim::addr_to_mem(reg_t addr) { return nullptr; }

bool error_done = false;

bool SpikeCosim::mmio_load(reg_t addr, size_t len, uint8_t *bytes) {
  return bus.load(addr, len, bytes);
}

bool SpikeCosim::mmio_store(reg_t addr, size_t len, const uint8_t *bytes) {
  return bus.store(addr, len, bytes);
}

void SpikeCosim::proc_reset(unsigned id) {}

const char *SpikeCosim::get_symbol(uint64_t addr) { return nullptr; }

void SpikeCosim::add_memory(uint32_t base_addr, size_t size) {
  auto new_mem = std::make_unique<mem_t>(size);
  bus.add_device(base_addr, new_mem.get());
  mems.emplace_back(std::move(new_mem));
}

bool SpikeCosim::backdoor_write_mem(uint32_t addr, size_t len,
                                    const uint8_t *data_in) {
  return bus.store(addr, len, data_in);
}

bool SpikeCosim::backdoor_read_mem(uint32_t addr, size_t len,
                                   uint8_t *data_out) {
  return bus.load(addr, len, data_out);
}

bool SpikeCosim::step(uint32_t write_reg, uint32_t write_reg_data,
                      uint32_t pc) {
  assert(write_reg < 32);

  // Execute the next instruction
  processor->step(1);

  while (processor->get_state()->last_inst_pc == PC_INVALID) {
    // When a trap occurrs no instruction will be execute and `last_inst_pc` will
    // be set to PC_INVALID. Rerun `step` until we execute a new instruction.
    processor->step(1);
  }

  // Check PC of executed instruction matches the expected PC
  if (processor->get_state()->last_inst_pc != pc) {
    std::stringstream err_str;
    err_str << "PC mismatch, DUT: " << std::hex << pc
            << " expected: " << std::hex << processor->get_state()->last_inst_pc
            << std::endl;
    errors.emplace_back(err_str.str());

    return false;
  }

  // Check register writes from executed instruction match what is expected
  auto &reg_changes = processor->get_state()->log_reg_write;

  bool gpr_write_seen = false;

  for (auto reg_change : reg_changes) {
    // reg_change.first provides register type in bottom 4 bits, then register
    // index above that

    // Ignore writes to x0
    if (reg_change.first == 0)
      continue;

    if ((reg_change.first & 0xf) == 0) {
      // register is GPR
      // should never see more than one GPR write per step
      assert(!gpr_write_seen);
      int cosim_write_reg = reg_change.first >> 4;

      if (write_reg == 0) {
        std::stringstream err_str;
        err_str << "DUT didn't write register, but one was expected to x"
                << std::dec << cosim_write_reg << std::endl;
        errors.emplace_back(err_str.str());

        return false;
      }

      if (write_reg != cosim_write_reg) {
        std::stringstream err_str;
        err_str << "Register write index mismatch, DUT: x" << std::dec
                << write_reg << " expected: x" << cosim_write_reg << std::endl;
        errors.emplace_back(err_str.str());

        return false;
      }

      uint32_t cosim_write_reg_data =
          static_cast<uint32_t>(reg_change.second.v[0]);

      if (write_reg_data != cosim_write_reg_data) {
        std::stringstream err_str;
        err_str << "Register write data mismatch to x" << std::dec
                << cosim_write_reg << " DUT: " << std::hex << write_reg_data
                << " expected: " << std::hex << cosim_write_reg_data
                << std::endl;
        errors.emplace_back(err_str.str());

        return false;
      }

      gpr_write_seen = true;
    } else if ((reg_change.first & 0xf) == 4) {
      // register is CSR
      // TODO: CSR write handling
    } else {
      // should never see other types
      assert(false);
    }
  }

  if (write_reg != 0 && !gpr_write_seen) {
    std::stringstream err_str;
    err_str << "DUT wrote register x" << std::dec << write_reg
            << " but a write was not expected" << std::endl;
    errors.emplace_back(err_str.str());

    return false;
  }

  return true;
}

void SpikeCosim::set_mip(uint32_t mip) { processor->get_state()->mip = mip; }

void SpikeCosim::set_debug_req(bool debug_req) {
  processor->halt_request =
      debug_req ? processor_t::HR_REGULAR : processor_t::HR_NONE;
}

const std::vector<std::string> &SpikeCosim::get_errors() { return errors; }

void SpikeCosim::clear_errors() { errors.clear(); }
