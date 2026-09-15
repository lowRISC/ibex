/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

// "RISC-V Formal Interface - Direct Instruction Injection" support
// For use with https://github.com/CTSRD-CHERI/TestRIG

$define RVFI_DII

bitfield RVFI_DII_Instruction_Packet : bits(64) = {
   padding   : 63 .. 56, // [7]
   rvfi_cmd  : 55 .. 48, // [6] This token is a trace command.  For example, reset device under test.
   rvfi_time : 47 .. 32, // [5 - 4] Time to inject token.  The difference between this and the previous
                         // instruction time gives a delay before injecting this instruction.
                         // This can be ignored for models but gives repeatability for implementations
                         // while shortening counterexamples.
   rvfi_insn : 31 ..  0, // [0 - 3] Instruction word: 32-bit instruction or command. The lower 16-bits
                         // may decode to a 16-bit compressed instruction.
}

register rvfi_instruction : RVFI_DII_Instruction_Packet

val rvfi_set_instr_packet : bits(64) -> unit

function rvfi_set_instr_packet(p) =
  rvfi_instruction = Mk_RVFI_DII_Instruction_Packet(p)

val rvfi_get_cmd : unit -> bits(8)

function rvfi_get_cmd () = rvfi_instruction[rvfi_cmd]

val rvfi_get_insn : unit -> bits(32)

function rvfi_get_insn () = rvfi_instruction[rvfi_insn]

val print_instr_packet : bits(64) -> unit

function print_instr_packet(bs) = {
  let p = Mk_RVFI_DII_Instruction_Packet(bs);
  print_bits("command ", p[rvfi_cmd]);
  print_bits("instruction ", p[rvfi_insn])
}

bitfield RVFI_DII_Execution_Packet_V1 : bits(704) = {
   rvfi_intr      : 703 .. 696, // [87] Trap handler:            Set for first instruction in trap handler.
   rvfi_halt      : 695 .. 688, // [86] Halt indicator:          Marks the last instruction retired
                                //                                      before halting execution.
   rvfi_trap      : 687 .. 680, // [85] Trap indicator:          Invalid decode, misaligned access or
                                //                                      jump command to misaligned address.
   rvfi_rd_addr   : 679 .. 672, // [84]      Write register address:  MUST be 0 if not used.
   rvfi_rs2_addr  : 671 .. 664, // [83]                          otherwise set as decoded.
   rvfi_rs1_addr  : 663 .. 656, // [82]      Read register addresses: Can be arbitrary when not used,
   rvfi_mem_wmask : 655 .. 648, // [81]      Write mask:              Indicates valid bytes written. 0 if unused.
   rvfi_mem_rmask : 647 .. 640, // [80]      Read mask:               Indicates valid bytes read. 0 if unused.
   rvfi_mem_wdata : 639 .. 576, // [72 - 79] Write data:              Data written to memory by this command.
   rvfi_mem_rdata : 575 .. 512, // [64 - 71] Read data:               Data read from mem_addr (i.e. before write)
   rvfi_mem_addr  : 511 .. 448, // [56 - 63] Memory access addr:      Points to byte address (aligned if define
                                //                                      is set). *Should* be straightforward.
                                //                                      0 if unused.
   rvfi_rd_wdata  : 447 .. 384, // [48 - 55] Write register value:    MUST be 0 if rd_ is 0.
   rvfi_rs2_data  : 383 .. 320, // [40 - 47]                          above. Must be 0 if register ID is 0.
   rvfi_rs1_data  : 319 .. 256, // [32 - 39] Read register values:    Values as read from registers named
   rvfi_insn      : 255 .. 192, // [24 - 31] Instruction word:        32-bit command value.
   rvfi_pc_wdata  : 191 .. 128, // [16 - 23] PC after instr:          Following PC - either PC + 4 or jump/trap target.
   rvfi_pc_rdata  : 127 ..  64, // [08 - 15] PC before instr:         PC for current instruction
   rvfi_order     :  63 ..   0, // [00 - 07] Instruction number:      INSTRET value after completion.
}

bitfield RVFI_DII_Execution_Packet_InstMetaData : bits(192) = {
  /// The rvfi_order field must be set to the instruction index. No indices
  /// must be used twice and there must be no gaps. Instructions may be
  /// retired in a reordered fashion, as long as causality is preserved
  /// (register and memory write operations must be retired before the read
  /// operations that depend on them).
  rvfi_order  : 63 .. 0,
  /// rvfi_insn is the instruction word for the retired instruction. In case
  /// of an instruction with fewer than ILEN bits, the upper bits of this
  /// output must be all zero. For compressed instructions the compressed
  /// instruction word must be output on this port. For fused instructions the
  /// complete fused instruction sequence must be output.
  rvfi_insn  : 127 ..  64,
  /// rvfi_trap must be set for an instruction that cannot be decoded as a
  /// legal instruction, such as 0x00000000.
  /// In addition, rvfi_trap must be set for a misaligned memory read or
  /// write in PMAs that don't allow misaligned access, or other memory
  /// access violations. rvfi_trap must also be set for a jump instruction
  /// that jumps to a misaligned instruction.
  rvfi_trap  : 135 ..  128,
  /// The signal rvfi_halt must be set when the instruction is the last
  /// instruction that the core retires before halting execution. It should not
  /// be set for an instruction that triggers a trap condition if the CPU
  /// reacts to the trap by executing a trap handler. This signal enables
  /// verification of liveness properties.
  rvfi_halt  : 143 ..  136,
  /// rvfi_intr must be set for the first instruction that is part of a trap
  /// handler, i.e. an instruction that has a rvfi_pc_rdata that does not
  /// match the rvfi_pc_wdata of the previous instruction.
  rvfi_intr  : 151 ..  144,
  /// rvfi_mode must be set to the current privilege level, using the following
  /// encoding: 0=U-Mode, 1=S-Mode, 2=Reserved, 3=M-Mode
  rvfi_mode  : 159 ..  152,
  /// rvfi_ixl must be set to the value of MXL/SXL/UXL in the current privilege level,
  /// using the following encoding: 1=32, 2=64
  rvfi_ixl  : 167 ..  160,

  /// When the core retires an instruction, it asserts the rvfi_valid signal
  /// and uses the signals described below to output the details of the
  /// retired instruction. The signals below are only valid during such a
  /// cycle and can be driven to arbitrary values in a cycle in which
  /// rvfi_valid is not asserted.
  rvfi_valid  : 175 ..  168,
  // Note: since we only send these packets in the valid state, we could
  // omit the valid signal, but we need 3 bytes of padding after ixl anyway
  // so we might as well include it
  padding  : 191 ..  176,
}

bitfield RVFI_DII_Execution_Packet_PC : bits(128) = {
  /// This is the program counter (pc) before (rvfi_pc_rdata) and after
  /// (rvfi_pc_wdata) execution of this instruction. I.e. this is the address
  /// of the retired instruction and the address of the next instruction.
  rvfi_pc_rdata  : 63 .. 0,
  rvfi_pc_wdata  : 127 ..  64,
}

bitfield RVFI_DII_Execution_Packet_Ext_Integer : bits(320) = {
  magic : 63 .. 0, // must be "int-data"
  /// rvfi_rd_wdata is the value of the x register addressed by rd after
  /// execution of this instruction. This output must be zero when rd is x0.
  rvfi_rd_wdata  : 127 ..  64,
  /// rvfi_rs1_rdata/rvfi_rs2_rdata is the value of the x register addressed
  /// by rs1/rs2 before execution of this instruction. This output must be
  /// zero when rs1/rs2 is x0.
  rvfi_rs1_rdata  : 191 .. 128,
  rvfi_rs2_rdata  : 255 .. 192,
  /// rvfi_rd_addr is the decoded rd register address for the retired
  /// instruction. For an instruction that writes no rd register, this output
  /// must always be zero.
  rvfi_rd_addr      : 263 .. 256,
  /// rvfi_rs1_addr and rvfi_rs2_addr are the decoded rs1 and rs1 register
  /// addresses for the retired instruction. For an instruction that reads no
  /// rs1/rs2 register, this output can have an arbitrary value. However, if
  /// this output is nonzero then rvfi_rs1_rdata must carry the value stored
  /// in that register in the pre-state.
  rvfi_rs1_addr  : 271 .. 264,
  rvfi_rs2_addr  : 279 .. 272,
  padding  : 319 .. 280,
}

bitfield RVFI_DII_Execution_Packet_Ext_MemAccess : bits(704) = {
  magic : 63 .. 0, // must be "mem-data"
  /// rvfi_mem_rdata is the pre-state data read from rvfi_mem_addr.
  /// rvfi_mem_rmask specifies which bytes are valid.
  /// CHERI-extension: widened to 32 bytes to allow reporting 129 bits
  rvfi_mem_rdata : 319 ..  64,
  /// rvfi_mem_wdata is the post-state data written to rvfi_mem_addr.
  /// rvfi_mem_wmask specifies which bytes are valid.
  /// CHERI-extension: widened to 32 bytes to allow reporting 129 bits
  rvfi_mem_wdata : 575 .. 320,
  /// rvfi_mem_rmask is a bitmask that specifies which bytes in rvfi_mem_rdata
  /// contain valid read data from rvfi_mem_addr.
  /// CHERI-extension: we extend rmask+wmask to 32 bits to allow reporting the
  /// mask for CHERI/RV128 accesses here.
  rvfi_mem_rmask      : 607 .. 576,
  /// rvfi_mem_wmask is a bitmask that specifies which bytes in rvfi_mem_wdata
  /// contain valid data that is written to rvfi_mem_addr.
  /// CHERI-extension: widened to 32 bits
  rvfi_mem_wmask      : 639 .. 608,
  /// For memory operations (rvfi_mem_rmask and/or rvfi_mem_wmask are
  /// non-zero), rvfi_mem_addr holds the accessed memory location.
  rvfi_mem_addr : 703 .. 640,
}

bitfield RVFI_DII_Execution_Packet_Ext_CSR : bits(208) = {
  magic : 63 .. 0, // must be "csr-data"
  /// rvfi_csr_rdata is the value of the control/status register addressed
  /// by csr before the execution of this instruction.
  /// This output must be zero when rd is x0.
  rvfi_csr_rdata : 127 .. 64,
  /// rvfi_csr_wdata is the value of the control/status register addressed
  /// by csr after the execution of this instruction.
  /// This output must be zero when rs1 is x0 or uimm is zero.
  rvfi_csr_wdata : 191 .. 128,
  /// rvfi_csr_addr is the decoded control/status register address
  /// for the retired instruction, zero-extended to 16-bits.
  rvfi_csr_addr : 207 .. 192,
}

bitfield RVFI_DII_Execution_Packet_Ext_CHERI : bits(496) = {
  magic : 63 .. 0, // must be "chericap"
  /// rvfi_cd_wdata is the value of the c register addressed by cd after
  /// execution of this instruction. This output must be zero when cd is c0.
  rvfi_cd_wdata : 191 .. 64,
  /// rvfi_cs1_rdata/rvfi_cs2_rdata is the value of the c register addressed
  /// by cs1/cs2 before execution of this instruction. This output must be
  /// zero when cs1/cs2 is c0.
  rvfi_cs1_rdata : 319 .. 192,
  rvfi_cs2_rdata : 447 .. 320,
  /// rvfi_cd_wdata is the value of the tag bit addressed by cd after
  /// execution of this instruction. This output must be zero when cd is c0.
  /// Pad to a whole byte to aid encoding/decoding.
  rvfi_cd_wtag  : 455 .. 448,
  /// rvfi_cs1_rtag/rvfi_cs2_rtag is the value of the tag bit addressed
  /// by cs1/cs2 before execution of this instruction. This output must be
  /// zero when cs1/cs2 is c0. Pad to a whole byte to aid encoding/decoding.
  rvfi_cs1_rtag  : 463 .. 456,
  rvfi_cs2_rtag  : 471 .. 464,
  /// rvfi_cd_addr is the decoded cd register address for the retired
  /// instruction. For an instruction that writes no cd register, this output
  /// must always be zero.
  rvfi_cd_addr  : 479 .. 472,
  /// rvfi_cs1_addr and rvfi_cs2_addr are the decoded cs1 and cs2 register
  /// addresses for the retired instruction. For an instruction that reads no
  /// cs1/rs2 register, this output can have an arbitrary value. However, if
  /// this output is nonzero then rvfi_cs1_rdata must carry the value stored
  /// in that register in the pre-state.
  rvfi_cs1_addr  : 487 .. 480,
  rvfi_cs2_addr  : 495 .. 488,
}

bitfield RVFI_DII_Execution_Packet_Ext_CHERI_SCR : bits(344) = {
  magic : 63 .. 0, // must be "cheriscr"
  /// rvfi_scr_rdata is the value of the special capability register addressed
  /// by scr before the execution of this instruction.
  /// There is NO requirement for this output to be zero when cd is c0.
  rvfi_scr_rdata : 191 .. 64,
  /// rvfi_scr_wdata is the value of the special capability register addressed
  /// by scr after the execution of this instruction.
  /// This output must be zero when cs1 is c0.
  rvfi_scr_wdata : 319 .. 192,
  /// rvfi_scr_rtag is the value of the tag bit addressed
  /// by scr before the execution of this instruction.
  /// There is NO requirement for this output to be zero when cd is c0.
  rvfi_scr_rtag : 327 .. 320,
  /// rvfi_scr_wtag is the value of the tag bit addressed
  /// by scr after the execution of this instruction.
  /// This output must be zero when cs1 is c0.
  rvfi_scr_wtag : 335 .. 328,
  /// rvfi_scr_addr is the decoded special capability register address
  /// for the retired instruction, zero-extended to 16-bits.
  /// See scr_name_map or the spec for a list of valid addresses.
  rvfi_scr_addr : 343 .. 336,
}

bitfield RVFI_DII_Execution_PacketV2 : bits(512) = {
  magic : 63 .. 0,         // must be set to 'trace-v2'
  trace_size : 127 .. 64,  // total size of the trace packet + extensions
  basic_data : 319 .. 128, // RVFI_DII_Execution_Packet_InstMetaData
  pc_data : 447 .. 320,    // RVFI_DII_Execution_Packet_PC
  // available_fields : 511 .. 448,
  integer_data_available: 448, // Followed by RVFI_DII_Execution_Packet_Ext_Integer if set
  memory_access_data_available: 449, // Followed by R VFI_DII_Execution_Packet_Ext_MemAccess if set
  floating_point_data_available: 450, // TODO: Followed by RVFI_DII_Execution_Packet_Ext_FP if set
  csr_read_write_data_available: 451, // Followed by RVFI_DII_Execution_Packet_Ext_CSR if set
  cheri_data_available: 452, // Followed by RVFI_DII_Execution_Packet_Ext_CHERI if set
  cheri_scr_read_write_data_available: 453, // Followed by RVFI_DII_Execution_Packet_Ext_CHERI_SCR if set
  trap_data_available: 454, // TODO: Followed by RVFI_DII_Execution_Packet_Ext_Trap if set
  unused_data_available_fields : 511 .. 455, // To be used for additional RVFI_DII_Execution_Packet_Ext_* structs
}

register rvfi_inst_data : RVFI_DII_Execution_Packet_InstMetaData
register rvfi_pc_data : RVFI_DII_Execution_Packet_PC
register rvfi_int_data : RVFI_DII_Execution_Packet_Ext_Integer
register rvfi_int_data_present : bool
register rvfi_mem_data : RVFI_DII_Execution_Packet_Ext_MemAccess
register rvfi_mem_data_present : bool
register rvfi_csr_data : RVFI_DII_Execution_Packet_Ext_CSR
register rvfi_csr_data_present : bool
register rvfi_cheri_data : RVFI_DII_Execution_Packet_Ext_CHERI
register rvfi_cheri_data_present : bool
register rvfi_cheri_scr_data : RVFI_DII_Execution_Packet_Ext_CHERI_SCR
register rvfi_cheri_scr_data_present : bool

// Reset the trace
val rvfi_zero_exec_packet : unit -> unit

function rvfi_zero_exec_packet () = {
  rvfi_inst_data = Mk_RVFI_DII_Execution_Packet_InstMetaData(zero_extend(0b0));

  rvfi_pc_data = Mk_RVFI_DII_Execution_Packet_PC(zero_extend(0b0));

  rvfi_int_data = Mk_RVFI_DII_Execution_Packet_Ext_Integer(zero_extend(0x0));
  // magic = "int-data" -> 0x617461642d746e69 (big-endian)
  rvfi_int_data = update_magic(rvfi_int_data, 0x617461642d746e69);
  rvfi_int_data_present = false;

  rvfi_mem_data = Mk_RVFI_DII_Execution_Packet_Ext_MemAccess(zero_extend(0x0));
  // magic = "mem-data" -> 0x617461642d6d656d (big-endian)
  rvfi_mem_data = update_magic(rvfi_mem_data, 0x617461642d6d656d);
  rvfi_mem_data_present = false;

  rvfi_csr_data = Mk_RVFI_DII_Execution_Packet_Ext_CSR(zero_extend(0x0));
  // magic = "csr-data" -> 0x617461642d727363 (big-endian)
  rvfi_csr_data = update_magic(rvfi_csr_data, 0x617461642d727363);
  rvfi_csr_data_present = false;

  rvfi_cheri_data = Mk_RVFI_DII_Execution_Packet_Ext_CHERI(zero_extend(0x0));
  // magic = "chericap" -> 0x7061636972656863 (big-endian)
  rvfi_cheri_data = update_magic(rvfi_cheri_data, 0x7061636972656863);
  rvfi_cheri_data_present = false;

  rvfi_cheri_scr_data = Mk_RVFI_DII_Execution_Packet_Ext_CHERI_SCR(zero_extend(0x0));
  // magic = "cheriscr" -> 0x7263736972656863 (big-endian)
  rvfi_cheri_scr_data = update_magic(rvfi_cheri_scr_data, 0x7263736972656863);
  rvfi_cheri_scr_data_present = false;
}

// FIXME: most of these will no longer be necessary once we use the c2 sail backend.

val rvfi_halt_exec_packet : unit -> unit

function rvfi_halt_exec_packet () =
  rvfi_inst_data->rvfi_halt() = 0x01

val rvfi_get_v2_support_packet : unit -> bits(704)
function rvfi_get_v2_support_packet () = {
  let rvfi_exec = Mk_RVFI_DII_Execution_Packet_V1(zero_extend(0b0));
  // Returning 0x3 (using the unused high bits) in halt instead of 0x1 means
  // that we support the version 2 wire format. This is required to keep
  // backwards compatibility with old implementations that do not support
  // the new trace format.
  let rvfi_exec = update_rvfi_halt(rvfi_exec, 0x03);
  return rvfi_exec.bits;
}

val rvfi_get_exec_packet_v1 : unit -> bits(704)
function rvfi_get_exec_packet_v1 () = {
  let v1_packet = Mk_RVFI_DII_Execution_Packet_V1(zero_extend(0b0));
  // Convert the v2 packet to a v1 packet
  let v1_packet = update_rvfi_intr(v1_packet, rvfi_inst_data[rvfi_intr]);
  let v1_packet = update_rvfi_halt(v1_packet, rvfi_inst_data[rvfi_halt]);
  let v1_packet = update_rvfi_trap(v1_packet, rvfi_inst_data[rvfi_trap]);
  let v1_packet = update_rvfi_insn(v1_packet, rvfi_inst_data[rvfi_insn]);
  let v1_packet = update_rvfi_order(v1_packet, rvfi_inst_data[rvfi_order]);

  let v1_packet = update_rvfi_pc_wdata(v1_packet, rvfi_pc_data[rvfi_pc_wdata]);
  let v1_packet = update_rvfi_pc_rdata(v1_packet, rvfi_pc_data[rvfi_pc_rdata]);

  let cheri_xd  = rvfi_cheri_data[rvfi_cd_addr]  != to_bits(8, 0);
  let cheri_xs1 = rvfi_cheri_data[rvfi_cs1_addr] != to_bits(8, 0);
  let cheri_xs2 = rvfi_cheri_data[rvfi_cs2_addr] != to_bits(8, 0);
  let xd_addr  = if cheri_xd  then rvfi_cheri_data[rvfi_cd_addr]  else rvfi_int_data[rvfi_rd_addr];
  let xs1_addr = if cheri_xs1 then rvfi_cheri_data[rvfi_cs1_addr] else rvfi_int_data[rvfi_rs1_addr];
  let xs2_addr = if cheri_xs2 then rvfi_cheri_data[rvfi_cs2_addr] else rvfi_int_data[rvfi_rs2_addr];
  let xd_wdata  = if cheri_xd  then truncate(rvfi_cheri_data[rvfi_cd_wdata],  64) else rvfi_int_data[rvfi_rd_wdata];
  let xs1_rdata = if cheri_xs1 then truncate(rvfi_cheri_data[rvfi_cs1_rdata], 64) else rvfi_int_data[rvfi_rs1_rdata];
  let xs2_rdata = if cheri_xs2 then truncate(rvfi_cheri_data[rvfi_cs2_rdata], 64) else rvfi_int_data[rvfi_rs2_rdata];
  let v1_packet = update_rvfi_rd_addr(v1_packet, xd_addr);
  let v1_packet = update_rvfi_rs2_addr(v1_packet, xs2_addr);
  let v1_packet = update_rvfi_rs1_addr(v1_packet, xs1_addr);
  let v1_packet = update_rvfi_rd_wdata(v1_packet, xd_wdata);
  let v1_packet = update_rvfi_rs2_data(v1_packet, xs2_rdata);
  let v1_packet = update_rvfi_rs1_data(v1_packet, xs1_rdata);

  let v1_packet = update_rvfi_mem_wmask(v1_packet, truncate(rvfi_mem_data[rvfi_mem_wmask], 8));
  let v1_packet = update_rvfi_mem_rmask(v1_packet, truncate(rvfi_mem_data[rvfi_mem_rmask], 8));
  let v1_packet = update_rvfi_mem_wdata(v1_packet, truncate(rvfi_mem_data[rvfi_mem_wdata], 64));
  let v1_packet = update_rvfi_mem_rdata(v1_packet, truncate(rvfi_mem_data[rvfi_mem_rdata], 64));
  let v1_packet = update_rvfi_mem_addr(v1_packet, rvfi_mem_data[rvfi_mem_addr]);

  return v1_packet.bits;
}

val rvfi_get_v2_trace_size : unit -> bits(64)
function rvfi_get_v2_trace_size () = {
  let trace_size : bits(64) = to_bits(64, 512);
  let trace_size = if (rvfi_int_data_present) then trace_size + 320 else trace_size;
  let trace_size = if (rvfi_mem_data_present) then trace_size + 704 else trace_size;
  let trace_size = if (rvfi_csr_data_present) then trace_size + 208 else trace_size;
  let trace_size = if (rvfi_cheri_data_present) then trace_size + 496 else trace_size;
  let trace_size = if (rvfi_cheri_scr_data_present) then trace_size + 344 else trace_size;
  return trace_size >> 3; // we have to return bytes not bits
}

val rvfi_get_exec_packet_v2 : unit -> bits(512)
function rvfi_get_exec_packet_v2 () = {
  // TODO: add the other data
  // TODO: find a way to return a variable-length bitvector
  let packet = Mk_RVFI_DII_Execution_PacketV2(zero_extend(0b0));
  let packet = update_magic(packet, 0x32762d6563617274); // ASCII "trace-v2" (BE)
  let packet = update_basic_data(packet, rvfi_inst_data.bits);
  let packet = update_pc_data(packet, rvfi_pc_data.bits);
  let packet = update_integer_data_available(packet, bool_to_bits(rvfi_int_data_present));
  let packet = update_memory_access_data_available(packet, bool_to_bits(rvfi_mem_data_present));
  let packet = update_csr_read_write_data_available(packet, bool_to_bits(rvfi_csr_data_present));
  let packet = update_cheri_data_available(packet, bool_to_bits(rvfi_cheri_data_present));
  let packet = update_cheri_scr_read_write_data_available(packet, bool_to_bits(rvfi_cheri_scr_data_present));
  // To simplify the implementation (so that we can return a fixed-size vector)
  // we always return a max-size packet from this function, and the C emulator
  // ensures that only trace_size bits are sent over the socket.
  let packet = update_trace_size(packet, rvfi_get_v2_trace_size());
  return packet.bits;
}

val rvfi_get_int_data : unit -> bits(320)
function rvfi_get_int_data () = {
  assert(rvfi_int_data_present, "reading uninitialized data");
  return rvfi_int_data.bits;
}

val rvfi_get_mem_data : unit -> bits(704)
function rvfi_get_mem_data () = {
  assert(rvfi_mem_data_present, "reading uninitialized data");
  return rvfi_mem_data.bits;
}

val rvfi_get_csr_data : unit -> bits(208)
function rvfi_get_csr_data () = {
  assert(rvfi_csr_data_present, "reading uninitialized data");
  return rvfi_csr_data.bits;
}

val rvfi_get_cheri_data : unit -> bits(496)
function rvfi_get_cheri_data () = {
  assert(rvfi_cheri_data_present, "reading uninitialized data");
  return rvfi_cheri_data.bits;
}

val rvfi_get_cheri_scr_data : unit -> bits(344)
function rvfi_get_cheri_scr_data () = {
  assert(rvfi_cheri_scr_data_present, "reading uninitialized data");
  return rvfi_cheri_scr_data.bits;
}

val rvfi_encode_width_mask : forall 'n, 0 < 'n <= 32. atom('n) -> bits(32)

function rvfi_encode_width_mask(width) =
  (0xFFFFFFFF >> (32 - width))

val print_rvfi_exec : unit -> unit

function print_rvfi_exec () = {
  print_bits("rvfi_intr     : ", rvfi_inst_data[rvfi_intr]);
  print_bits("rvfi_halt     : ", rvfi_inst_data[rvfi_halt]);
  print_bits("rvfi_trap     : ", rvfi_inst_data[rvfi_trap]);
  print_bits("rvfi_csr_addr : ", rvfi_csr_data[rvfi_csr_addr]);
  print_bits("rvfi_csr_wdata: ", rvfi_csr_data[rvfi_csr_wdata]);
  print_bits("rvfi_csr_rdata: ", rvfi_csr_data[rvfi_csr_rdata]);
  print_bits("rvfi_scr_addr : ", rvfi_cheri_scr_data[rvfi_scr_addr]);
  print_bits("rvfi_scr_wdata: ", rvfi_cheri_scr_data[rvfi_scr_wdata]);
  print_bits("rvfi_scr_rdata: ", rvfi_cheri_scr_data[rvfi_scr_rdata]);
  print_bits("rvfi_rd_addr  : ", rvfi_int_data[rvfi_rd_addr]);
  print_bits("rvfi_rs2_addr : ", rvfi_int_data.rvfi_rs2_addr());
  print_bits("rvfi_rs1_addr : ", rvfi_int_data.rvfi_rs1_addr());
  print_bits("rvfi_cd_addr  : ", rvfi_cheri_data[rvfi_cd_addr]);
  print_bits("rvfi_cs2_addr : ", rvfi_cheri_data.rvfi_cs2_addr());
  print_bits("rvfi_cs1_addr : ", rvfi_cheri_data.rvfi_cs1_addr());
  print_bits("rvfi_mem_wmask: ", rvfi_mem_data[rvfi_mem_wmask]);
  print_bits("rvfi_mem_rmask: ", rvfi_mem_data[rvfi_mem_rmask]);
  print_bits("rvfi_mem_wdata: ", rvfi_mem_data[rvfi_mem_wdata]);
  print_bits("rvfi_mem_rdata: ", rvfi_mem_data[rvfi_mem_rdata]);
  print_bits("rvfi_mem_addr : ", rvfi_mem_data[rvfi_mem_addr]);
  print_bits("rvfi_rd_wdata : ", rvfi_int_data[rvfi_rd_wdata]);
  print_bits("rvfi_rs2_data : ", rvfi_int_data.rvfi_rs2_rdata());
  print_bits("rvfi_rs1_data : ", rvfi_int_data.rvfi_rs1_rdata());
  print_bits("rvfi_cd_wdata : ", rvfi_cheri_data[rvfi_cd_wdata]);
  print_bits("rvfi_cs2_data : ", rvfi_cheri_data.rvfi_cs2_rdata());
  print_bits("rvfi_cs1_data : ", rvfi_cheri_data.rvfi_cs1_rdata());
  print_bits("rvfi_cd_wtag : ", rvfi_cheri_data[rvfi_cd_wtag]);
  print_bits("rvfi_cs2_tag : ", rvfi_cheri_data.rvfi_cs2_rtag());
  print_bits("rvfi_cs1_tag : ", rvfi_cheri_data.rvfi_cs1_rtag());
  print_bits("rvfi_insn     : ", rvfi_inst_data[rvfi_insn]);
  print_bits("rvfi_pc_wdata : ", rvfi_pc_data[rvfi_pc_wdata]);
  print_bits("rvfi_pc_rdata : ", rvfi_pc_data[rvfi_pc_rdata]);
  print_bits("rvfi_order    : ", rvfi_inst_data[rvfi_order]);
}
