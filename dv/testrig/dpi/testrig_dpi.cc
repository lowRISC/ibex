#include <svdpi.h>
#include <cassert>
#include <iostream>
#include "testrig.hh"
#include "testrig_dpi.h"

TestRIG::Connection* testrig_create(const int port) {
  return new TestRIG::Connection(port);
}

svBit testrig_get_next_instruction(TestRIG::Connection* conn,
    svBitVecVal* dii_insn, svBitVecVal* dii_time, svBitVecVal* dii_cmd) {

  assert(conn);

  TestRIG::RVFI_DII_Instruction_Packet insn_pkt;

  if (conn->get_next_instruction(insn_pkt, 100)) {
    *dii_insn = insn_pkt.dii_insn;
    *dii_time = static_cast<uint32_t>(insn_pkt.dii_time);
    *dii_cmd = static_cast<uint32_t>(insn_pkt.dii_cmd);

    return 1;
  }

  return 0;
}

void testrig_send_rvfi_halt(TestRIG::Connection* conn) {
  TestRIG::RVFI_DII_Execution_Packet rstpacket = {
      .rvfi_halt = 1
  };

  conn->put_execution(rstpacket);
}

void testrig_send_exec_pkt(TestRIG::Connection* conn, svBitVecVal* pkt_val) {
  TestRIG::RVFI_DII_Execution_Packet exec_pkt;

  exec_pkt = *reinterpret_cast<TestRIG::RVFI_DII_Execution_Packet*>(pkt_val);

  conn->put_execution(exec_pkt);
  //std::cout << "Got an exec packet\n";

  //for (int i = 0;i < 23; ++i) {
  //  std::cout << std::hex << (uint32_t) pkt_val[i] << std::endl;
  //}

  //std::cout << "order: " << std::hex << exec_pkt.rvfi_order << " rvfi_insn: "
  //  << std::hex << exec_pkt.rvfi_insn << " rvfi_mem_wdata: " << std::hex
  //  << exec_pkt.rvfi_mem_wdata << " rvfi_intr: " << std::hex
  //  << (uint32_t) exec_pkt.rvfi_intr << std::endl;
}
