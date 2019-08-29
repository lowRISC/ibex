// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "register_transaction.h"

#include <iostream>

void RegisterTransaction::Randomize(std::default_random_engine &gen) {
  std::uniform_int_distribution<int> addr_dist_ =
      std::uniform_int_distribution<int>(kCSRPMPCfg0, kCSRPMPAddr15);
  std::uniform_int_distribution<int> wdata_dist_ =
      std::uniform_int_distribution<int>(0, 0xFFFFFFFF);
  std::uniform_int_distribution<int> operation_dist_ =
      std::uniform_int_distribution<int>(kCSRRead, kCSRClear);
  csr_addr = addr_dist_(gen);
  csr_op = static_cast<CSRegisterOperation>(operation_dist_(gen));
  if (csr_op != kCSRRead) {
    csr_wdata = wdata_dist_(gen);
  }
}

void RegisterTransaction::Print() {
  std::cout << "Register transaction:" << std::endl
            << "Operation:  " << RegOpString() << std::endl
            << "Address:    " << RegAddrString() << std::endl;
  if (csr_op != kCSRRead) {
    std::cout << "Write data: " << std::hex << csr_wdata << std::endl;
  }
  std::cout << "Read data:  " << std::hex << csr_rdata << std::dec << std::endl;
}

std::string RegisterTransaction::RegOpString() {
  switch (csr_op) {
    case kCSRRead:
      return "CSR Read";
    case kCSRWrite:
      return "CSR Write";
    case kCSRSet:
      return "CSR Set";
    case kCSRClear:
      return "CSR Clear";
    default:
      return "Unknown op";
  }
}

std::string RegisterTransaction::RegAddrString() {
  switch (csr_addr) {
    case kCSRPMPCfg0:
      return "PMP Cfg 0";
    case kCSRPMPCfg1:
      return "PMP Cfg 1";
    case kCSRPMPCfg2:
      return "PMP Cfg 2";
    case kCSRPMPCfg3:
      return "PMP Cfg 3";
    case kCSRPMPAddr0:
      return "PMP Addr 0";
    case kCSRPMPAddr1:
      return "PMP Addr 1";
    case kCSRPMPAddr2:
      return "PMP Addr 2";
    case kCSRPMPAddr3:
      return "PMP Addr 3";
    case kCSRPMPAddr4:
      return "PMP Addr 4";
    case kCSRPMPAddr5:
      return "PMP Addr 5";
    case kCSRPMPAddr6:
      return "PMP Addr 6";
    case kCSRPMPAddr7:
      return "PMP Addr 7";
    case kCSRPMPAddr8:
      return "PMP Addr 8";
    case kCSRPMPAddr9:
      return "PMP Addr 9";
    case kCSRPMPAddr10:
      return "PMP Addr 10";
    case kCSRPMPAddr11:
      return "PMP Addr 11";
    case kCSRPMPAddr12:
      return "PMP Addr 12";
    case kCSRPMPAddr13:
      return "PMP Addr 13";
    case kCSRPMPAddr14:
      return "PMP Addr 14";
    case kCSRPMPAddr15:
      return "PMP Addr 15";
    default:
      return "Undef reg: " + std::to_string(csr_addr);
  }
}
