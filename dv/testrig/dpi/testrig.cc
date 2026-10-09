#include "testrig.hh"
#include "socket_packet_utils.c"

#include <chrono>
#include <iostream>

namespace TestRIG {

// TODO: May make sense to rewrite these to ditch the use of
// 'socket_packet_utils.c'. In particular we don't need non-blocking socket IO
// due to the use of dedicated send/received threads.

void Connection::receive_thread_main() {
   char recbuf[sizeof(RVFI_DII_Instruction_Packet) + 1] = {0};

   RVFI_DII_Instruction_Packet *instruction_pkt;

   while (true) {
     serv_socket_getN((unsigned int *) recbuf, socket,
        sizeof(RVFI_DII_Instruction_Packet));

     if (recbuf[sizeof(RVFI_DII_Instruction_Packet)] == 0) {
       instruction_pkt =
         reinterpret_cast<RVFI_DII_Instruction_Packet *>(recbuf);

       instruction_pkt_q.produce(*instruction_pkt);
     } else {
       std::this_thread::sleep_for(std::chrono::milliseconds(1));
     }
   }
}

void Connection::send_thread_main() {
  while (true) {
     RVFI_DII_Execution_Packet execution_pkt = execution_pkt_q.consume();

     while(!serv_socket_putN(socket, sizeof(RVFI_DII_Execution_Packet),
             reinterpret_cast<unsigned int*>(&execution_pkt)));
  }
}

bool Connection::get_next_instruction(
    RVFI_DII_Instruction_Packet& instruction_pkt, std::uint32_t timeout_ms) {

  return instruction_pkt_q.consume_wait(instruction_pkt, timeout_ms);
}

void Connection::put_execution(RVFI_DII_Execution_Packet& execution_pkt) {
  execution_pkt_q.produce(execution_pkt);
}

Connection::Connection(std::uint32_t port) {
  socket = serv_socket_create_nameless(port);
  serv_socket_init(socket);

  receive_thread = std::thread([=]() { receive_thread_main(); });
  send_thread = std::thread([=]() { send_thread_main(); });
}

}; // namespace TestRIG
