// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef REGISTER_TRANSACTION_H_
#define REGISTER_TRANSACTION_H_

#include <stdint.h>
#include <random>
#include <string>

// Enumerate the four register operation types
enum CSRegisterOperation : int {
  kCSRRead = 0,
  kCSRWrite = 1,
  kCSRSet = 2,
  kCSRClear = 3
};

// Enumerate the supported register types
enum CSRegisterAddr : int {
  kCSRPMPCfg0 = 0x3A0,
  kCSRPMPCfg1 = 0x3A1,
  kCSRPMPCfg2 = 0x3A2,
  kCSRPMPCfg3 = 0x3A3,
  kCSRPMPAddr0 = 0x3B0,
  kCSRPMPAddr1 = 0x3B1,
  kCSRPMPAddr2 = 0x3B2,
  kCSRPMPAddr3 = 0x3B3,
  kCSRPMPAddr4 = 0x3B4,
  kCSRPMPAddr5 = 0x3B5,
  kCSRPMPAddr6 = 0x3B6,
  kCSRPMPAddr7 = 0x3B7,
  kCSRPMPAddr8 = 0x3B8,
  kCSRPMPAddr9 = 0x3B9,
  kCSRPMPAddr10 = 0x3BA,
  kCSRPMPAddr11 = 0x3BB,
  kCSRPMPAddr12 = 0x3BC,
  kCSRPMPAddr13 = 0x3BD,
  kCSRPMPAddr14 = 0x3BE,
  kCSRPMPAddr15 = 0x3BF
};

struct RegisterTransaction {
 public:
  void Randomize(std::default_random_engine &gen);
  void Print();

  CSRegisterOperation csr_op;
  bool illegal_csr;
  uint32_t csr_addr;
  uint32_t csr_rdata;
  uint32_t csr_wdata;

 private:
  std::string RegOpString();
  std::string RegAddrString();
};

#endif  // REGISTER_TRANSACTION_H_
