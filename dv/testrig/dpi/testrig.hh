#pragma once

#include <queue>
#include <thread>
#include <mutex>
#include <condition_variable>

namespace TestRIG {

// The layout of this must match the layout of the testrig_rvfi_exec_pkt_t
// structure in testrig_dpi.svh. WARNING: The fields listed here are in reverse
// order compared to SystemVerilog.
struct RVFI_DII_Execution_Packet {
  std::uint64_t rvfi_order : 64;      // [00 - 07] Instruction number:      INSTRET value after completion.
  std::uint64_t rvfi_pc_rdata : 64;   // [08 - 15] PC before instr:         PC for current instruction
  std::uint64_t rvfi_pc_wdata : 64;   // [16 - 23] PC after instr:          Following PC - either PC + 4 or jump/trap target.
  std::uint64_t rvfi_insn : 64;       // [24 - 31] Instruction word:        32-bit command value.
  std::uint64_t rvfi_rs1_data : 64;   // [32 - 39] Read register values:    Values as read from registers named
  std::uint64_t rvfi_rs2_data : 64;   // [40 - 47]                          above. Must be 0 if register ID is 0.
  std::uint64_t rvfi_rd_wdata : 64;   // [48 - 55] Write register value:    MUST be 0 if rd_ is 0.
  std::uint64_t rvfi_mem_addr : 64;   // [56 - 63] Memory access addr:      Points to byte address (aligned if define
                                      //                                      is set). *Should* be straightforward.
                                      //                                      0 if unused.
  std::uint64_t rvfi_mem_rdata : 64;  // [64 - 71] Read data:               Data read from mem_addr (i.e. before write)
  std::uint64_t rvfi_mem_wdata : 64;  // [72 - 79] Write data:              Data written to memory by this command.
  std::uint8_t rvfi_mem_rmask : 8;    // [80]      Read mask:               Indicates valid bytes read. 0 if unused.
  std::uint8_t rvfi_mem_wmask : 8;    // [81]      Write mask:              Indicates valid bytes written. 0 if unused.
  std::uint8_t rvfi_rs1_addr : 8;     // [82]      Read register addresses: Can be arbitrary when not used,
  std::uint8_t rvfi_rs2_addr : 8;     // [83]                               otherwise set as decoded.
  std::uint8_t rvfi_rd_addr : 8;      // [84]      Write register address:  MUST be 0 if not used.
  std::uint8_t rvfi_trap : 8;         // [85] Trap indicator:               Invalid decode, misaligned access or
                                      //                                      jump command to misaligned address.
  std::uint8_t rvfi_halt : 8;         // [86] Halt indicator:               Marks the last instruction retired
                                      //                                      before halting execution.
  std::uint8_t rvfi_intr : 8;         // [87] Trap handler:                 Set for first instruction in trap handler.
};

struct RVFI_DII_Instruction_Packet {
  std::uint32_t dii_insn : 32;      // [0 - 3] Instruction word: 32-bit instruction or command. The lower 16-bits
                                    // may decode to a 16-bit compressed instruction.
  std::uint16_t dii_time : 16;      // [5 - 4] Time to inject token.  The difference between this and the previous
                                    // instruction time gives a delay before injecting this instruction.
                                    // This can be ignored for models but gives repeatability for implementations
                                    // while shortening counterexamples.
  std::uint8_t dii_cmd : 8;         // [6] This token is a trace command.  For example, reset device under test.
  std::uint8_t padding : 8;         // [7]
};

template <typename T>
class ProducerConsumer {
  private:
    std::queue<T> queue;
    std::mutex mutex;
    std::condition_variable cv;
  public:
    void produce(const T& item) {
      std::lock_guard<std::mutex> lock(mutex);

      queue.push(item);
      cv.notify_all();
    }

    bool consume_wait(T& item_out, std::uint32_t timeout_ms) {
      std::unique_lock<std::mutex> lock(mutex);

      if(cv.wait_for(lock, std::chrono::milliseconds(timeout_ms),
          [=] { return !queue.empty(); })) {
        item_out = queue.front();
        queue.pop();

        return true;
      }

      return false;
    }

    T consume() {
      std::unique_lock<std::mutex> lock(mutex);

      cv.wait(lock, [=] { return !queue.empty(); });

      auto item = queue.front();
      queue.pop();

      return item;
    }
};

class Connection {
  private:
    ProducerConsumer<RVFI_DII_Instruction_Packet> instruction_pkt_q;
    ProducerConsumer<RVFI_DII_Execution_Packet> execution_pkt_q;
    std::thread receive_thread;
    std::thread send_thread;

    unsigned long long socket;

    void receive_thread_main();
    void send_thread_main();
  public:
    Connection(std::uint32_t port);

    bool get_next_instruction(RVFI_DII_Instruction_Packet& instruction_pkt,
      std::uint32_t timeout_ms);
    void put_execution(RVFI_DII_Execution_Packet& execution_pkt);
};

}; // namespace TestRIG
