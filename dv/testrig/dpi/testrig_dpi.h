// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef TESTRIG_DPI_H_
#define TESTRIG_DPI_H_


#include <stdint.h>
#include <svdpi.h>
#include "testrig.hh"

extern "C" {
TestRIG::Connection* testrig_create(const int port);
svBit testrig_get_next_instruction(TestRIG::Connection* conn,
    svBitVecVal* dii_insn, svBitVecVal* dii_time, svBitVecVal* dii_cmd);
void testrig_send_rvfi_halt(TestRIG::Connection*  conn);
void testrig_send_exec_pkt(TestRIG::Connection* conn, svBitVecVal* pkt_val);
}

#endif
