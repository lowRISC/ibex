// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Step 2: DPI bridge between cheriot-sail generated C and UVM cosim scoreboard.
//
// Wraps zinit_model / zrvfi_set_instr_packet / zstep / zrvfi_get_cheri_data
// in an extern "C" interface callable from SystemVerilog via DPI.
// This is a global singleton — the Sail model uses process-wide global state.

#include "cheriot_sail_cosim_dpi.h"

#include <cassert>
#include <cstdio>
#include <cstring>
#include <string>
#include <vector>
// svBitVecVal = uint32_t, svBit = unsigned char (from IEEE 1800 / svdpi.h).
// Defined here so we can compile without Xcelium headers.
typedef uint32_t      svBitVecVal;
typedef unsigned char svBit;

// Include gmp.h first in C++ context so its inline C++ stream operators are
// declared before sail.h re-requests it inside an extern "C" block (where
// extern "C++" nesting causes compiler errors on some GCC versions).
#include <gmp.h>

extern "C" {
// sail.h will try to #include <gmp.h> but include guards make it a no-op;
// the C++ operators are already registered above.
#include "sail.h"
#include "riscv_rvfi_model_RV32.h"

// model_init / model_fini are defined in the generated C but not declared in
// the generated header (they live in the .c only).
void model_init(void);
void model_fini(void);

// Required callbacks referenced by riscv_platform.c / riscv_platform_impl.c
// but defined in riscv_sim.c (which we exclude to avoid its main()).
bool config_print_instr       = false;
bool config_print_reg         = false;
bool config_print_mem_access  = false;
bool config_print_platform    = false;
bool config_print_exception   = false;
FILE *trace_log               = nullptr;

// write_mem is defined in the generated model C code; declare it here so we
// can call it from cheriot_sail_cosim_write_mem_byte.
void write_mem(uint64_t addr, uint64_t byte_val);

// Externally-visible memory layout globals (riscv_platform_impl.c)
extern uint64_t rv_ram_base;
extern uint64_t rv_ram_size;
extern uint64_t rv_rom_base;
extern uint64_t rv_rom_size;
extern uint64_t rv_htif_tohost;
}  // extern "C"

// ---------------------------------------------------------------------------
// Module state
// ---------------------------------------------------------------------------
static bool s_initialized = false;
static int64_t s_step_no  = 0;
static std::vector<std::string> s_errors;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

// Retrieve the CHERI extension packet and extract the two scalar fields we
// check in the initial integration step: capability destination register
// address and write-tag bit.
static void get_cheri_output(uint64_t *out_cd_addr, uint64_t *out_cd_wtag) {
  lbits raw;
  CREATE(lbits)(&raw);
  zrvfi_get_cheri_data(&raw, UNIT);

  // The field accessors take the struct wrapper by value, sharing the lbits
  // pointer.  Call them before KILL(raw).
  struct zRVFI_DII_Execution_Packet_Ext_CHERI pkt = {.zbits = raw};
  *out_cd_addr = z_get_RVFI_DII_Execution_Packet_Ext_CHERI_rvfi_cd_addr(pkt);
  *out_cd_wtag = z_get_RVFI_DII_Execution_Packet_Ext_CHERI_rvfi_cd_wtag(pkt);

  KILL(lbits)(&raw);
}

// ---------------------------------------------------------------------------
// DPI interface
// ---------------------------------------------------------------------------

void cheriot_sail_cosim_init(const svBitVecVal *boot_addr_p) {
  uint32_t boot_addr = boot_addr_p[0];
  fprintf(stderr, "[cheriot-sail] init: boot_addr=0x%08x\n", boot_addr);
  if (s_initialized) {
    fprintf(stderr, "[cheriot-sail] init: re-initializing (calling model_fini first)\n");
    model_fini();
  }
  fprintf(stderr, "[cheriot-sail] init: calling model_init\n");
  model_init();
  fprintf(stderr, "[cheriot-sail] init: calling zinit_model\n");
  zinit_model(UNIT);
  fprintf(stderr, "[cheriot-sail] init: calling zext_rvfi_init\n");
  zext_rvfi_init(UNIT);
  fprintf(stderr, "[cheriot-sail] init: zext_rvfi_init done\n");

  // CHERIoT-Ibex RVFI-DII mode: no ROM, RAM starts at 0x80000000.
  // These globals are in riscv_platform_impl.c, linked into our .so.
  rv_ram_base    = UINT64_C(0x80000000);
  rv_ram_size    = UINT64_C(0x800000);
  rv_rom_base    = UINT64_C(0);
  rv_rom_size    = UINT64_C(0);
  rv_htif_tohost = UINT64_C(0);

  // Set PC and mtvec to match CHERIoT-Ibex reset behaviour (from riscv_sim.c).
  zPC             = (uint64_t)boot_addr;
  zmtvec.zbits    = (uint64_t)boot_addr;

  s_step_no = 0;
  s_errors.clear();
  s_initialized = true;
  fprintf(stderr, "[cheriot-sail] init: complete, PC=0x%08llx\n", (unsigned long long)zPC);
}

int cheriot_sail_cosim_step(const svBitVecVal *insn_p,
                             const svBitVecVal *pc_p,
                             svBit cheri_rf_we,
                             const svBitVecVal *cheri_rd_p,
                             svBit cheri_rtag) {
  uint32_t insn     = insn_p[0];
  uint32_t pc       = pc_p[0];
  uint32_t cheri_rd = cheri_rd_p[0];
  assert(s_initialized && "cheriot_sail_cosim_init() must be called first");

  if (s_step_no < 5 || (s_step_no % 50 == 0)) {
    fprintf(stderr, "[cheriot-sail] step %lld: insn=0x%08x pc=0x%08x\n",
            (long long)s_step_no, insn, pc);
  }

  // Debug: print Sail internal state for steps near the trap to diagnose
  // "step failed (not stepped)" — covers dispatchInterrupt check and fetch state.
  if (s_step_no >= 60 && s_step_no <= 70) {
    fprintf(stderr, "[cheriot-sail] INSN step %lld: insn=0x%08x rtl_pc=0x%08x\n",
            (long long)s_step_no, (unsigned)insn, (unsigned)pc);
  }
  if (s_step_no >= 60) {
    uint64_t mip_bits = zmip.zbits;
    uint64_t mie_bits = zmie.zbits;
    uint64_t mst_bits = zmstatus.zbits;
    uint64_t sail_pc  = zPC;
    uint64_t mie_flag = z_get_Mstatus_MIE(zmstatus);
    fprintf(stderr,
            "[cheriot-sail] DBG step %lld: sail_pc=0x%08llx nextPC=0x%08llx rtl_pc=0x%08x mstatus=0x%llx MIE=%llu mip=0x%llx mie=0x%llx pending=0x%llx\n",
            (long long)s_step_no,
            (unsigned long long)sail_pc,
            (unsigned long long)znextPC,
            (unsigned)pc,
            (unsigned long long)mst_bits,
            (unsigned long long)mie_flag,
            (unsigned long long)mip_bits,
            (unsigned long long)mie_bits,
            (unsigned long long)(mip_bits & mie_bits));
  }

  // Encode RVFI-DII instruction packet (Sail bitfield RVFI_DII_Instruction_Packet):
  //   bits[31: 0] = rvfi_insn  (instruction word)
  //   bits[47:32] = rvfi_time  (step sequence number, 16-bit)
  //   bits[55:48] = rvfi_cmd   (0x01 = execute-instruction)
  //   bits[63:56] = reserved
  uint64_t pkt = (uint64_t)insn
               | ((uint64_t)(s_step_no & 0xffff) << 32)
               | ((uint64_t)0x01 << 48);
  zrvfi_set_instr_packet(pkt);
  // Clear the execution output packet before each step (mirrors riscv_sim.c).
  zrvfi_zzero_exec_packet(UNIT);

  // Enable Sail instruction tracing for steps near the trap.
  bool was_print_instr = config_print_instr;
  FILE *was_trace_log = trace_log;
  if (s_step_no >= 63 && s_step_no <= 67) {
    config_print_instr = true;
    config_print_exception = true;
    trace_log = stderr;
  }

  // Sync Sail's PC to ibex's current instruction PC before every step.
  // This prevents drift from (a) silent Error_not_rv32e_register retires on x16-x31
  // accesses and (b) trap-skip gaps where ibex jumps to a handler but Sail doesn't.
  // zPCC.zaddress is the cursor used by CAUIPCC/ext_fetch_check_pc; keep it in sync.
  zPC = (uint64_t)pc;
  zPCC.zaddress = (uint64_t)pc;

  sail_int sail_step;
  CREATE(sail_int)(&sail_step);
  CONVERT_OF(sail_int, mach_int)(&sail_step, s_step_no);
  // zstep() returns true when an instruction was actually stepped (success).
  bool stepped = zstep(sail_step);
  config_print_instr = was_print_instr;
  config_print_exception = false;
  trace_log = was_trace_log;
  KILL(sail_int)(&sail_step);

  // Post-step debug: show what happened
  if (s_step_no >= 60) {
    fprintf(stderr,
            "[cheriot-sail] POST step %lld: sail_pc=0x%08llx nextPC=0x%08llx MIE=%llu mip=0x%llx mstatus=0x%llx stepped=%d\n",
            (long long)s_step_no,
            (unsigned long long)zPC,
            (unsigned long long)znextPC,
            (unsigned long long)z_get_Mstatus_MIE(zmstatus),
            (unsigned long long)zmip.zbits,
            (unsigned long long)zmstatus.zbits,
            (int)stepped);
  }

  s_step_no++;

  if (!stepped) {
    fprintf(stderr, "[cheriot-sail] step failed (not stepped) at step %lld\n", (long long)(s_step_no - 1));
    s_errors.emplace_back("cheriot-sail model failed to step at step " +
                          std::to_string(s_step_no - 1));
    return -1;
  }

  // Only compare CHERI output when the Sail model executed a CHERIoT capability
  // instruction (zrvfi_cheri_data_present is true).  For ordinary integer
  // instructions both tag and address are uninitialized in the model's output
  // packet; calling zrvfi_get_cheri_data() would trigger a sail_assert failure.
  if (!zrvfi_cheri_data_present) return 0;

  uint64_t sail_cd_addr = 0, sail_cd_wtag = 0;
  get_cheri_output(&sail_cd_addr, &sail_cd_wtag);
  fprintf(stderr, "[cheriot-sail] CHERI step %lld: sail_cd_addr=%llu sail_cd_wtag=%llu | rtl_we=%d rtl_rd=%d rtl_tag=%d\n",
          (long long)(s_step_no - 1),
          (unsigned long long)sail_cd_addr, (unsigned long long)(sail_cd_wtag & 1),
          (int)cheri_rf_we, (int)cheri_rd, (int)cheri_rtag);

  // Skip if Sail reports no capability destination (cd_addr=0, cd_wtag=0).
  // Integer-result CHERI instructions (cgettag, cgetlen, etc.) don't write a
  // capability in Sail's model; ibex nullifies the register but Sail doesn't.
  // Writing to c0 with tag=0 is also a no-op and safe to skip.
  if (sail_cd_addr == 0 && sail_cd_wtag == 0) return 0;

  // Also skip if the RTL didn't write a capability register this cycle.
  if (!cheri_rf_we) return 0;

  int ok = 1;

  if (sail_cd_addr != (uint64_t)cheri_rd) {
    char buf[160];
    snprintf(buf, sizeof(buf),
             "cheriot-sail cd_addr mismatch: sail=0x%02llx rtl=0x%02x "
             "(insn=0x%08x pc=0x%08x step=%lld)",
             (unsigned long long)sail_cd_addr, (unsigned)cheri_rd,
             (unsigned)insn, (unsigned)pc, (long long)(s_step_no - 1));
    s_errors.emplace_back(buf);
    ok = 0;
  }

  if ((sail_cd_wtag & 1) != (uint64_t)((unsigned)cheri_rtag & 1)) {
    char buf[160];
    snprintf(buf, sizeof(buf),
             "cheriot-sail cd_wtag mismatch: sail=%llu rtl=%u "
             "(insn=0x%08x pc=0x%08x step=%lld)",
             (unsigned long long)(sail_cd_wtag & 1), (unsigned)cheri_rtag & 1,
             (unsigned)insn, (unsigned)pc, (long long)(s_step_no - 1));
    s_errors.emplace_back(buf);
    ok = 0;
  }

  return ok ? 0 : -1;
}

// Return the Sail model's mtval register value after the last zstep().
// Only meaningful when the last step took a trap (rvfi_trap == 1).
uint32_t cheriot_sail_cosim_get_mtval(void) {
  return (uint32_t)(zmtval & 0xffffffffULL);
}

int cheriot_sail_cosim_get_num_errors(void) {
  return (int)s_errors.size();
}

const char *cheriot_sail_cosim_get_error(int index) {
  if (index < 0 || (size_t)index >= s_errors.size()) return nullptr;
  return s_errors[(size_t)index].c_str();
}

void cheriot_sail_cosim_clear_errors(void) {
  s_errors.clear();
}

// Load one byte into the Sail model's memory (call after init, before first step).
void cheriot_sail_cosim_cleanup(void) {
  if (s_initialized) {
    model_fini();
    s_initialized = false;
  }
  s_step_no = 0;
  s_errors.clear();
}

// Load one byte into the Sail model's memory (call after init, before first step).
void cheriot_sail_cosim_write_mem_byte(const svBitVecVal *addr_p, svBit data) {
  assert(s_initialized);
  write_mem((uint64_t)addr_p[0], (uint64_t)data);
}
