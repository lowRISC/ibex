// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * This tracer takes execution information from the RISC-V Verification Interface (RVFI) and
 * produces a text file with a human-readable trace.
 *
 * All traced instructions are written to a log file. By default, the log file is named
 * traceNNNN.log, with NNNN being the 4 digit hart ID of the core being traced.
 *
 * The file name base, defaulting to "trace" can be set using the "traceFile"
 * plusarg passed to the simulation, e.g. "+traceFile=trace". The exact syntax
 * of passing plusargs to a simulation depends on the simulator.
 *
 * The trace contains produces 3 types of entries that can be enabled separately 
 * Instruction trace, enabled by trace_enable_inst consistes of the following entries:
 * - The simulation timestamp tttttttttttt uu
 * - The program counter      PC=0xiiiiiiii,
 * - The instruction code     0xcccccccc or 0xcccc, for compressed instruction
 * - The decoded instruction  in the specification format
 * Memory trace enabled by trace_enable_mem
 * - The simulation timestamp tttttttttttt uu
 * - The address written/read MW/MR=0xaaaaaaaa,
 * - The written/read value   0xvvvvvvvv
 * Register trace enabled by trace_enable_reg
 * - The simulation timestamp tttttttttttt uu
 * - The register changed     REG=x[0..31],
 * - The new value            0xvvvvvvvv
 *
 */
module ibex_tracer #(
  parameter int unsigned HartId                   = 32'h0
) 
(
  input logic        clk_i,
  input logic        rst_ni,

  // RVFI as described at https://github.com/SymbioticEDA/riscv-formal/blob/master/docs/rvfi.md
  // The standard interface does not have _i/_o suffixes. For consistency with the standard the
  // signals in this module don't have the suffixes either.
  input logic        rvfi_valid,
  input logic [63:0] rvfi_order,
  input logic [31:0] rvfi_insn,
  input logic        rvfi_trap,
  input logic        rvfi_halt,
  input logic        rvfi_intr,
  input logic [ 1:0] rvfi_mode,
  input logic [ 1:0] rvfi_ixl,
  input logic [ 4:0] rvfi_rs1_addr,
  input logic [ 4:0] rvfi_rs2_addr,
  input logic [ 4:0] rvfi_rs3_addr,
  input logic [31:0] rvfi_rs1_rdata,
  input logic [31:0] rvfi_rs2_rdata,
  input logic [31:0] rvfi_rs3_rdata,
  input logic [ 4:0] rvfi_rd_addr,
  input logic [31:0] rvfi_rd_wdata,
  input logic [31:0] rvfi_pc_rdata,
  input logic [31:0] rvfi_pc_wdata,
  input logic [31:0] rvfi_mem_addr,
  input logic [ 3:0] rvfi_mem_rmask,
  input logic [ 3:0] rvfi_mem_wmask,
  input logic [31:0] rvfi_mem_rdata,
  input logic [31:0] rvfi_mem_wdata
);
  import ibex_tracer_pkg::*;

  // Data items accessed during this instruction
  localparam bit [4:0] RS1 = (1 << 0);
  localparam bit [4:0] RS2 = (1 << 1);
  localparam bit [4:0] RS3 = (1 << 2);
  localparam bit [4:0] RD  = (1 << 3);
  localparam bit [4:0] MEM = (1 << 4);

  // These signals are part of RVFI, but not used in this module currently.
  // Keep them as part of the interface to change the tracer more easily in the future. Assigning
  // these signals to unused_* signals marks them explicitly as unused, an annotation picked up by
  // linters, including Verilator lint.
  logic [63:0]   unused_rvfi_order = rvfi_order;
  logic          unused_rvfi_trap = rvfi_trap;
  logic          unused_rvfi_halt = rvfi_halt;
  logic          unused_rvfi_intr = rvfi_intr;
  logic [ 1:0]   unused_rvfi_mode = rvfi_mode;

  int            file_handle;
  bit [16*8-1:0] file_name;
  bit [31*8-1:0] decoded_str;

  time           tstamp;
  logic [4:0]    data_accessed;
  bit            insn_is_compressed;
  bit            trace_enable_inst;    // pragma keep_net trace_enable_inst
  bit            trace_enable_reg;     // pragma keep_net trace_enable_reg
  bit            trace_enable_mem;     // pragma keep_net trace_enable_mem
  
  initial begin
`ifdef IXCOM_UXE
    $ixc_ctrl("gfifo", "$fwrite");
`endif
    trace_enable_inst = $test$plusargs("traceI") ? 1'b1 : 1'b0;
    trace_enable_reg = $test$plusargs("traceR") ? 1'b1 : 1'b0;
    trace_enable_mem = $test$plusargs("traceM") ? 1'b1 : 1'b0;
    if( trace_enable_inst | trace_enable_reg | trace_enable_mem ) begin
      if (!$value$plusargs("traceFile=%s", file_name)) file_name = "trace_";
      file_handle[7:0]   = {4'h0,HartId[3:0]} + (HartId[3:0] > 4'h9 ? 8'h57 : 8'h30);
      file_handle[15:8]  = {4'h0,HartId[7:4]} + (HartId[7:4] > 4'h9 ? 8'h57 : 8'h30);
      file_handle[23:16] = {4'h0,HartId[11:8]} + (HartId[11:8] > 4'h9 ? 8'h57 : 8'h30);
      file_handle[31:24] = {4'h0,HartId[15:12]} + (HartId[15:12] > 4'h9 ? 8'h57 : 8'h30);
      file_name = {file_name[8*8-1:0], file_handle[31:0], ".log"};
      file_handle = $fopen(file_name, "w");
      $display("%m: Writing execution trace to %s", file_name);
    end else begin
      file_handle = 'h0;
    end
`ifndef VERILATOR
    $timeformat(-9, 0, " ns", 14);
`endif
  end

  final begin
    if( file_handle ) begin
      $fclose( file_handle );
    end
  end
  
  // get 2 digit hex string
  function automatic bit [2*8-1:0] to_hex2( input bit [7:0] val );
    bit [2*8-1:0] str;
    str[15:8] = val[7:4] + (val[7:4] > 4'h9 ? 8'h57 : 8'h30);
    str[7:0] = val[3:0] + (val[3:0] > 4'h9 ? 8'h57 : 8'h30);
    return str;
  endfunction

  // get 3 digit hex string
  function automatic bit [3*8-1:0] to_hex3( input bit [11:0] val );
    bit [3*8-1:0] str;
    str[23:16] = val[11:8] + (val[11:8] > 4'h9 ? 8'h57 : 8'h30);
    str[15:8] = val[7:4] + (val[7:4] > 4'h9 ? 8'h57 : 8'h30);
    str[7:0] = val[3:0] + (val[3:0] > 4'h9 ? 8'h57 : 8'h30);
    return str;
  endfunction

  // get 5 digit hex string
  function automatic bit [5*8-1:0] to_hex5( input bit [19:0] val );
    return {to_hex2(val[19:12]),to_hex3(val[11:0])};
  endfunction

  // get 8 digit hex string
  function automatic bit [8*8-1:0] to_hex8( input bit [31:0] val );
    return {to_hex3(val[31:20]),to_hex2(val[19:12]),to_hex3(val[11:0])};
  endfunction

  // get 12b offset as string +/-0xddd
  function automatic bit [6*8-1:0] to_offset12( input bit [11:0] val );
    bit [6*8-1:0] str;
    bit [11:0] off;
    if( val[11] ) begin
      off = ~val + 1;
      str = {"-0x", to_hex3(off)};
    end else begin
      str = {"+0x", to_hex3(val)};
    end
    return str;
  endfunction

  // get 6b offset as string +/-0xdd
  function automatic bit [5*8-1:0] to_offset6( input bit [5:0] val );
    bit [5*8-1:0] str;
    bit [5:0] off;
    if( val[5] ) begin
      off = ~val + 1;
      str = {"-0x", to_hex2(off)};
    end else begin
      str = {"+0x", to_hex2(val)};
    end
    return str;
  endfunction

  // Get a register name for a reg address.
  function automatic bit [3*8-1:0] get_reg_name(input bit [4:0] reg_addr);
    unique case (reg_addr)
      5'd00 : return " x0";
      5'd01 : return " x1";
      5'd02 : return " x2";
      5'd03 : return " x3";
      5'd04 : return " x4";
      5'd05 : return " x5";
      5'd06 : return " x6";
      5'd07 : return " x7";
      5'd08 : return " x8";
      5'd09 : return " x9";
      5'd10 : return "x10";
      5'd11 : return "x11";
      5'd12 : return "x12";
      5'd13 : return "x13";
      5'd14 : return "x14";
      5'd15 : return "x15";      
      5'd16 : return "x16";
      5'd17 : return "x17";
      5'd18 : return "x18";
      5'd19 : return "x19";
      5'd20 : return "x20";
      5'd21 : return "x21";
      5'd22 : return "x22";
      5'd23 : return "x23";
      5'd24 : return "x24";
      5'd25 : return "x25";
      5'd26 : return "x26";
      5'd27 : return "x27";
      5'd28 : return "x28";
      5'd29 : return "x29";
      5'd30 : return "x30";
      5'd31 : return "x31";
    endcase
  endfunction

  // Get a CSR name for a CSR address.
  function automatic bit [14*8-1:0] get_csr_name(input bit [11:0] csr_addr);
    unique case (csr_addr)
      12'h000: return "       ustatus";
      12'h001: return "        fflags";
      12'h002: return "           frm";
      12'h003: return "          fcsr";
      12'h004: return "           uie";
      12'h005: return "         utvec";
      12'h040: return "      uscratch";
      12'h041: return "          uepc";
      12'h042: return "        ucause";
      12'h043: return "         utval";
      12'h044: return "           uip";
      12'h100: return "       sstatus";
      12'h102: return "       sedeleg";
      12'h103: return "       sideleg";
      12'h104: return "           sie";
      12'h105: return "         stvec";
      12'h106: return "    scounteren";
      12'h140: return "      sscratch";
      12'h141: return "          sepc";
      12'h142: return "        scause";
      12'h143: return "         stval";
      12'h144: return "           sip";
      12'h180: return "          satp";
      12'h200: return "       hstatus";
      12'h202: return "       hedeleg";
      12'h203: return "       hideleg";
      12'h204: return "           hie";
      12'h205: return "         htvec";
      12'h240: return "      hscratch";
      12'h241: return "          hepc";
      12'h242: return "        hcause";
      12'h243: return "      hbadaddr";
      12'h244: return "           hip";
      12'h300: return "       mstatus";
      12'h301: return "          misa";
      12'h302: return "       medeleg";
      12'h303: return "       mideleg";
      12'h304: return "           mie";
      12'h305: return "         mtvec";
      12'h306: return "    mcounteren";
      12'h320: return "   mucounteren";
      12'h321: return "   mscounteren";
      12'h322: return "   mhcounteren";
      12'h323: return "    mhpmevent3";
      12'h324: return "    mhpmevent4";
      12'h325: return "    mhpmevent5";
      12'h326: return "    mhpmevent6";
      12'h327: return "    mhpmevent7";
      12'h328: return "    mhpmevent8";
      12'h329: return "    mhpmevent9";
      12'h32a: return "   mhpmevent10";
      12'h32b: return "   mhpmevent11";
      12'h32c: return "   mhpmevent12";
      12'h32d: return "   mhpmevent13";
      12'h32e: return "   mhpmevent14";
      12'h32f: return "   mhpmevent15";
      12'h330: return "   mhpmevent16";
      12'h331: return "   mhpmevent17";
      12'h332: return "   mhpmevent18";
      12'h333: return "   mhpmevent19";
      12'h334: return "   mhpmevent20";
      12'h335: return "   mhpmevent21";
      12'h336: return "   mhpmevent22";
      12'h337: return "   mhpmevent23";
      12'h338: return "   mhpmevent24";
      12'h339: return "   mhpmevent25";
      12'h33a: return "   mhpmevent26";
      12'h33b: return "   mhpmevent27";
      12'h33c: return "   mhpmevent28";
      12'h33d: return "   mhpmevent29";
      12'h33e: return "   mhpmevent30";
      12'h33f: return "   mhpmevent31";
      12'h340: return "      mscratch";
      12'h341: return "          mepc";
      12'h342: return "        mcause";
      12'h343: return "         mtval";
      12'h344: return "           mip";
      12'h380: return "         mbase";
      12'h381: return "        mbound";
      12'h382: return "        mibase";
      12'h383: return "       mibound";
      12'h384: return "        mdbase";
      12'h385: return "       mdbound";
      12'h3a0: return "       pmpcfg0";
      12'h3a1: return "       pmpcfg1";
      12'h3a2: return "       pmpcfg2";
      12'h3a3: return "       pmpcfg3";
      12'h3b0: return "      pmpaddr0";
      12'h3b1: return "      pmpaddr1";
      12'h3b2: return "      pmpaddr2";
      12'h3b3: return "      pmpaddr3";
      12'h3b4: return "      pmpaddr4";
      12'h3b5: return "      pmpaddr5";
      12'h3b6: return "      pmpaddr6";
      12'h3b7: return "      pmpaddr7";
      12'h3b8: return "      pmpaddr8";
      12'h3b9: return "      pmpaddr9";
      12'h3ba: return "     pmpaddr10";
      12'h3bb: return "     pmpaddr11";
      12'h3bc: return "     pmpaddr12";
      12'h3bd: return "     pmpaddr13";
      12'h3be: return "     pmpaddr14";
      12'h3bf: return "     pmpaddr15";
      12'h7a0: return "       tselect";
      12'h7a1: return "        tdata1";
      12'h7a2: return "        tdata2";
      12'h7a3: return "        tdata3";
      12'h7a4: return "         tinfo";
      12'h7a5: return "      tcontrol";
      12'h7b0: return "          dcsr";
      12'h7b1: return "           dpc";
      12'h7b2: return "     dscratch0";
      12'h7b3: return "     dscratch1";
      12'hb00: return "        mcycle";
      12'hb02: return "      minstret";
      12'hb03: return "  mhpmcounter3";
      12'hb04: return "  mhpmcounter4";
      12'hb05: return "  mhpmcounter5";
      12'hb06: return "  mhpmcounter6";
      12'hb07: return "  mhpmcounter7";
      12'hb08: return "  mhpmcounter8";
      12'hb09: return "  mhpmcounter9";
      12'hb0a: return " mhpmcounter10";
      12'hb0b: return " mhpmcounter11";
      12'hb0c: return " mhpmcounter12";
      12'hb0d: return " mhpmcounter13";
      12'hb0e: return " mhpmcounter14";
      12'hb0f: return " mhpmcounter15";
      12'hb10: return " mhpmcounter16";
      12'hb11: return " mhpmcounter17";
      12'hb12: return " mhpmcounter18";
      12'hb13: return " mhpmcounter19";
      12'hb14: return " mhpmcounter20";
      12'hb15: return " mhpmcounter21";
      12'hb16: return " mhpmcounter22";
      12'hb17: return " mhpmcounter23";
      12'hb18: return " mhpmcounter24";
      12'hb19: return " mhpmcounter25";
      12'hb1a: return " mhpmcounter26";
      12'hb1b: return " mhpmcounter27";
      12'hb1c: return " mhpmcounter28";
      12'hb1d: return " mhpmcounter29";
      12'hb1e: return " mhpmcounter30";
      12'hb1f: return " mhpmcounter31";
      12'hb80: return "       mcycleh";
      12'hb82: return "     minstreth";
      12'hb83: return " mhpmcounter3h";
      12'hb84: return " mhpmcounter4h";
      12'hb85: return " mhpmcounter5h";
      12'hb86: return " mhpmcounter6h";
      12'hb87: return " mhpmcounter7h";
      12'hb88: return " mhpmcounter8h";
      12'hb89: return " mhpmcounter9h";
      12'hb8a: return "mhpmcounter10h";
      12'hb8b: return "mhpmcounter11h";
      12'hb8c: return "mhpmcounter12h";
      12'hb8d: return "mhpmcounter13h";
      12'hb8e: return "mhpmcounter14h";
      12'hb8f: return "mhpmcounter15h";
      12'hb90: return "mhpmcounter16h";
      12'hb91: return "mhpmcounter17h";
      12'hb92: return "mhpmcounter18h";
      12'hb93: return "mhpmcounter19h";
      12'hb94: return "mhpmcounter20h";
      12'hb95: return "mhpmcounter21h";
      12'hb96: return "mhpmcounter22h";
      12'hb97: return "mhpmcounter23h";
      12'hb98: return "mhpmcounter24h";
      12'hb99: return "mhpmcounter25h";
      12'hb9a: return "mhpmcounter26h";
      12'hb9b: return "mhpmcounter27h";
      12'hb9c: return "mhpmcounter28h";
      12'hb9d: return "mhpmcounter29h";
      12'hb9e: return "mhpmcounter30h";
      12'hb9f: return "mhpmcounter31h";
      12'hc00: return "         cycle";
      12'hc01: return "          time";
      12'hc02: return "       instret";
      12'hc03: return "   hpmcounter3";
      12'hc04: return "   hpmcounter4";
      12'hc05: return "   hpmcounter5";
      12'hc06: return "   hpmcounter6";
      12'hc07: return "   hpmcounter7";
      12'hc08: return "   hpmcounter8";
      12'hc09: return "   hpmcounter9";
      12'hc0a: return "  hpmcounter10";
      12'hc0b: return "  hpmcounter11";
      12'hc0c: return "  hpmcounter12";
      12'hc0d: return "  hpmcounter13";
      12'hc0e: return "  hpmcounter14";
      12'hc0f: return "  hpmcounter15";
      12'hc10: return "  hpmcounter16";
      12'hc11: return "  hpmcounter17";
      12'hc12: return "  hpmcounter18";
      12'hc13: return "  hpmcounter19";
      12'hc14: return "  hpmcounter20";
      12'hc15: return "  hpmcounter21";
      12'hc16: return "  hpmcounter22";
      12'hc17: return "  hpmcounter23";
      12'hc18: return "  hpmcounter24";
      12'hc19: return "  hpmcounter25";
      12'hc1a: return "  hpmcounter26";
      12'hc1b: return "  hpmcounter27";
      12'hc1c: return "  hpmcounter28";
      12'hc1d: return "  hpmcounter29";
      12'hc1e: return "  hpmcounter30";
      12'hc1f: return "  hpmcounter31";
      12'hc80: return "        cycleh";
      12'hc81: return "         timeh";
      12'hc82: return "      instreth";
      12'hc83: return "  hpmcounter3h";
      12'hc84: return "  hpmcounter4h";
      12'hc85: return "  hpmcounter5h";
      12'hc86: return "  hpmcounter6h";
      12'hc87: return "  hpmcounter7h";
      12'hc88: return "  hpmcounter8h";
      12'hc89: return "  hpmcounter9h";
      12'hc8a: return " hpmcounter10h";
      12'hc8b: return " hpmcounter11h";
      12'hc8c: return " hpmcounter12h";
      12'hc8d: return " hpmcounter13h";
      12'hc8e: return " hpmcounter14h";
      12'hc8f: return " hpmcounter15h";
      12'hc90: return " hpmcounter16h";
      12'hc91: return " hpmcounter17h";
      12'hc92: return " hpmcounter18h";
      12'hc93: return " hpmcounter19h";
      12'hc94: return " hpmcounter20h";
      12'hc95: return " hpmcounter21h";
      12'hc96: return " hpmcounter22h";
      12'hc97: return " hpmcounter23h";
      12'hc98: return " hpmcounter24h";
      12'hc99: return " hpmcounter25h";
      12'hc9a: return " hpmcounter26h";
      12'hc9b: return " hpmcounter27h";
      12'hc9c: return " hpmcounter28h";
      12'hc9d: return " hpmcounter29h";
      12'hc9e: return " hpmcounter30h";
      12'hc9f: return " hpmcounter31h";
      12'hf11: return "     mvendorid";
      12'hf12: return "       marchid";
      12'hf13: return "        mimpid";
      12'hf14: return "       mhartid";
      default: return {"0x",to_hex3(csr_addr)};
    endcase
  endfunction

  function automatic void decode_mnemonic(input bit[8*8-1:0] mnemonic);
    decoded_str = {mnemonic, {23{8'h20}}};
  endfunction

  function automatic void decode_cjr_insn(input bit[8*8-1:0] mnemonic);
    if (rvfi_insn[12] == 1'b1) begin
      data_accessed = RS1 | RD;  // C.JALR = jalr x1
    end else begin
      data_accessed = RS1;       // C.JR   = jr x0
    end
    decoded_str = {mnemonic, get_reg_name(rvfi_rs1_addr), {20{8'h20}}};
  endfunction

  function automatic void decode_cmv_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RS2 | RD; // RS1 == RD
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs2_addr), {16{8'h20}}};
  endfunction

  function automatic void decode_cr_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RS2 | RD; // RS1 == RD
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs2_addr), {12{8'h20}}};
  endfunction

  function automatic void decode_cli_insn(input bit[8*8-1:0] mnemonic);
    bit [5:0] imm;
    imm = {rvfi_insn[12], rvfi_insn[6:2]};
    data_accessed = RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", to_offset6(imm), {14{8'h20}}};
  endfunction

  function automatic void decode_caddi_insn(input bit[8*8-1:0] mnemonic);
    bit [5:0] nzimm;
    nzimm = {rvfi_insn[12], rvfi_insn[6:2]};
    data_accessed = RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rd_addr), ",", to_offset6(nzimm), {10{8'h20}}};
  endfunction

  function automatic void decode_caddisp_insn(input bit[8*8-1:0] mnemonic);
    bit [11:0] nzimm;
    if (rvfi_insn[0] == 1'b1) begin    // C.ADDI16SPN
      nzimm = {rvfi_insn[12], rvfi_insn[12], rvfi_insn[12], rvfi_insn[4:3], rvfi_insn[5], rvfi_insn[2], rvfi_insn[6], 4'b0};
    end else begin                     // C.ADDI4SPN
      nzimm = {2'b00, rvfi_insn[10:7], rvfi_insn[12:11], rvfi_insn[5], rvfi_insn[6], 2'b00};
    end
    data_accessed = RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ", x2,", to_offset12(nzimm), {9{8'h20}}};
  endfunction

  function automatic void decode_clui_insn(input bit[8*8-1:0] mnemonic);
    bit [5:0] nzimm;
    nzimm = {rvfi_insn[12], rvfi_insn[6:2]};
    data_accessed = RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",0x", to_hex2(nzimm), {15{8'h20}}};
  endfunction

  function automatic void decode_clogi_insn(input bit[8*8-1:0] mnemonic);
    bit [5:0] shamt;                   // C.ANDI, C.SRAI C.SRLI C.SLLI
    shamt = {rvfi_insn[12], rvfi_insn[6:2]};
    data_accessed = RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rd_addr), ",0x", to_hex2(shamt), {11{8'h20}}};
  endfunction

  function automatic void decode_cb_insn(input bit[8*8-1:0] mnemonic);
    bit [7:0] imm;
    bit [31:0] target;
    imm = {rvfi_insn[12], rvfi_insn[6:5], rvfi_insn[2], rvfi_insn[11:10], rvfi_insn[4:3]};
    target = rvfi_pc_rdata + 32'($signed({imm, 1'b0})); // cannot use rvfi_pc_wdata for branches
    data_accessed = RS1;
    decoded_str = {mnemonic, get_reg_name(rvfi_rs1_addr), ",0x", to_hex8(target), {9{8'h20}}};
  endfunction

  function automatic void decode_cj_insn(input bit[8*8-1:0] mnemonic);
    if (rvfi_insn[15:13] == 3'b001) begin
      data_accessed = RD;             // C.JAL = jal x1
    end
    decoded_str = {mnemonic, "0x", to_hex8(rvfi_pc_wdata), {13{8'h20}}};
  endfunction

  function automatic void decode_cload_insn(input bit[8*8-1:0] mnemonic);
    bit [7:0] imm;

    if (rvfi_insn[1:0] == OPCODE_C0) begin
      // C.LW
      imm = {1'b0, rvfi_insn[5], rvfi_insn[12:10], rvfi_insn[6], 2'b00};
    end else begin
      // C.LWSP
      imm = {rvfi_insn[3:2], rvfi_insn[12], rvfi_insn[6:4], 2'b00};
    end
    data_accessed = RS1 | RD | MEM;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",0x", to_hex2(imm), "(", get_reg_name(rvfi_rs1_addr), ")", {10{8'h20}}};
  endfunction

  function automatic void decode_cstore_insn(input bit[8*8-1:0] mnemonic);
    bit [7:0] imm;
    if (rvfi_insn[1:0] == OPCODE_C0) begin
      // C.SW
      imm = {1'b0, rvfi_insn[5], rvfi_insn[12:10], rvfi_insn[6], 2'b00};
    end else begin
      // C.SWSP
      imm = {rvfi_insn[8:7], rvfi_insn[12:9], 2'b00};
    end
    data_accessed = RS1 | RS2 | MEM;
    decoded_str = {mnemonic, get_reg_name(rvfi_rs2_addr), ",0x", to_hex2(imm),  "(", get_reg_name(rvfi_rs1_addr), ")", {10{8'h20}}};
  endfunction

  function automatic void decode_r_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RS1 | RS2 | RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs1_addr), ",", get_reg_name(rvfi_rs2_addr), {12{8'h20}}};
  endfunction

  function automatic void decode_r2_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RS1 | RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs1_addr), {16{8'h20}}};
  endfunction

  function automatic void decode_i_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RS1 | RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs1_addr), ",", to_offset12(rvfi_insn[31:20]), {9{8'h20}}};
  endfunction

  function automatic void decode_i_log_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RS1 | RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs1_addr), ",0x", to_hex3(rvfi_insn[31:20]), {10{8'h20}}};
  endfunction

  function automatic void decode_i_shift_insn(input bit[8*8-1:0] mnemonic);
    // SLLI, SRLI, SRAI
    data_accessed = RS1 | RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs1_addr), ",0x", to_hex2({3'b000,rvfi_insn[24:20]}), {11{8'h20}}};
  endfunction

  function automatic void decode_i_jalr_insn(input bit[8*8-1:0] mnemonic);
    if (rvfi_rd_addr != 5'h0) begin
      data_accessed = RS1 | RD;        // JALR
    end else begin
      data_accessed = RS1;             // JR
    end
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", to_offset12(rvfi_insn[31:20]), "(", get_reg_name(rvfi_rs1_addr), ")", {8{8'h20}}};
  endfunction

  function automatic void decode_u_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",0x", to_hex5(rvfi_insn[31:12]), {12{8'h20}}};
  endfunction

  function automatic void decode_j_insn(input bit[8*8-1:0] mnemonic);
    if (rvfi_rd_addr != 5'h0) begin
      data_accessed = RD;              // JAL else J
    end
    decoded_str = {mnemonic, "0x", to_hex8(rvfi_pc_wdata), {13{8'h20}}};
  endfunction

  function automatic void decode_b_insn(input bit[8*8-1:0] mnemonic);
    bit [31:0] target;
    bit [12:0] imm;
    imm = {rvfi_insn[31], rvfi_insn[7], rvfi_insn[30:25], rvfi_insn[11:8], 1'b0};
    target = rvfi_pc_rdata + 32'($signed(imm)); // cannot use rvfi_pc_wdata for branches;
    data_accessed = RS1 | RS2;
    decoded_str = {mnemonic, get_reg_name(rvfi_rs1_addr), ",", get_reg_name(rvfi_rs2_addr), ",0x", to_hex8(target), {5{8'h20}}};
  endfunction

  function automatic void decode_csr_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RD;
    if (!rvfi_insn[14]) begin
      data_accessed |= RS1;
      decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_csr_name(rvfi_insn[31:20]), ",", get_reg_name(rvfi_rs1_addr), 8'h20};
    end else begin
      decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_csr_name(rvfi_insn[31:20]), ",0x", to_hex2(rvfi_insn[19:15])};
    end
  endfunction

  function automatic void decode_load_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RD | RS1 | MEM;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", to_offset12(rvfi_insn[31:20]), "(", get_reg_name(rvfi_rs1_addr), ")", {8{8'h20}}};
  endfunction

  function automatic void decode_store_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RS1 | RS2 | MEM;
    decoded_str = {mnemonic, get_reg_name(rvfi_rs2_addr), ",", to_offset12({rvfi_insn[31:25], rvfi_insn[11:7]}), "(", get_reg_name(rvfi_rs1_addr), ")", {8{8'h20}}};
  endfunction

  function automatic bit[4*8-1:0] get_fence_flags(input bit [3:0] bits);
    bit[4*8-1:0] desc;
    desc[31:24] = (bits[3] ? "i" : "_" );
    desc[23:16] = (bits[2] ? "o" : "_" );
    desc[15:8]  = (bits[1] ? "r" : "_" );
    desc[7:0]   = (bits[0] ? "w" : "_" );
    return desc;
  endfunction

  function automatic void decode_fence(input bit[8*8-1:0] mnemonic);
    decoded_str = {mnemonic, get_fence_flags(rvfi_insn[27:24]), ",", get_fence_flags(rvfi_insn[23:20]), {14{8'h20}}};
  endfunction

  function automatic void decode_r4c_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RS1 | RS2 | RS3 | RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs2_addr), ",", get_reg_name(rvfi_rs1_addr), ",", get_reg_name(rvfi_rs3_addr), {8{8'h20}}}; 
  endfunction

  function automatic void decode_r4fs_insn(input bit[8*8-1:0] mnemonic);
    data_accessed = RS1 | RS2 | RS3 | RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs1_addr), ",", get_reg_name(rvfi_rs3_addr), ",", get_reg_name(rvfi_rs2_addr), {8{8'h20}}}; 
  endfunction

  function automatic void decode_i_fs_insn( input bit[8*8-1:0] mnemonic);
￼    // fsri
￼    bit [7:0] shamt;
￼    shamt = {2'b0, rvfi_insn[25:20]};
￼    data_accessed = RS1 | RS3 | RD;
    decoded_str = {mnemonic, get_reg_name(rvfi_rd_addr), ",", get_reg_name(rvfi_rs1_addr), ",", get_reg_name(rvfi_rs3_addr), ",0x", to_hex2(shamt), {5{8'h20}}};
￼  endfunction

  // trace write function
  function automatic void printbuffer_dumpline();
    tstamp = $time;
    if( trace_enable_inst ) begin
      if (insn_is_compressed) begin
        $fwrite(file_handle, "%t PC=0x%8h,     0x%04h, %s\n", tstamp, rvfi_pc_rdata, rvfi_insn[15:0], decoded_str);
      end else begin
        $fwrite(file_handle, "%t PC=0x%8h, 0x%08x, %s\n", tstamp, rvfi_pc_rdata, rvfi_insn, decoded_str);
      end
    end
    if ( trace_enable_mem && (data_accessed & MEM) != 0 ) begin
      if (rvfi_mem_wmask != 4'b000) begin
        $fwrite(file_handle, "%t MW=0x%08x, 0x%08x\n", tstamp, rvfi_mem_addr, rvfi_mem_wdata);
      end else if (rvfi_mem_rmask != 4'b000) begin     
        $fwrite(file_handle, "%t MR=0x%08x, 0x%08x\n", tstamp, rvfi_mem_addr, rvfi_mem_rdata);
      end
    end
    if ( trace_enable_reg && (data_accessed & RD) != 0) begin
      $fwrite(file_handle, "%t REG=%s, 0x%08x\n", tstamp, get_reg_name(rvfi_rd_addr), rvfi_rd_wdata);
    end
  endfunction

  // log execution
  always_ff @(posedge clk_i) begin
    if (rvfi_valid) begin
      printbuffer_dumpline();
    end
  end

  always_comb begin
    decoded_str = "";
    data_accessed = 5'h0;

    // Check for compressed instructions
    if (rvfi_insn[1:0] != 2'b11) begin
      insn_is_compressed = 1;
      unique casez (rvfi_insn[15:0])
        // C0 Opcodes
        INSN_CADDI4SPN:
                   decode_caddisp_insn("addi    ");
        INSN_CLW:    decode_cload_insn("lw      ");
        INSN_CSW:   decode_cstore_insn("sw      ");
        // C1 Opcodes
        INSN_CADDI: if (rvfi_insn[11:2] == 10'h0)
                       decode_mnemonic("nop     ");
                    else
                     decode_caddi_insn("addi    ");
        INSN_CJAL:      decode_cj_insn("jal     ");
        INSN_CJ:        decode_cj_insn("j       ");
        INSN_CLI:      decode_cli_insn("li      ");
        INSN_CLUI: if (rvfi_insn[11:7] == 5'h2)
                   decode_caddisp_insn("addi    ");
                   else
                      decode_clui_insn("lui     ");
        INSN_CSRLI:  decode_clogi_insn("srli    ");
        INSN_CSRAI:  decode_clogi_insn("srai    ");
        INSN_CANDI:  decode_clogi_insn("andi    ");
        INSN_CSUB:      decode_cr_insn("sub     ");
        INSN_CXOR:      decode_cr_insn("xor     ");
        INSN_COR:       decode_cr_insn("or      ");
        INSN_CAND:      decode_cr_insn("and     ");
        INSN_CBEQZ:     decode_cb_insn("beqz    ");
        INSN_CBNEZ:     decode_cb_insn("bnez    ");
        // C2 Opcodes
        INSN_CSLLI:  decode_clogi_insn("slli    ");
        INSN_CLWSP:  decode_cload_insn("lw      ");
        INSN_CMV:  if (rvfi_insn[6:2] == 5'h0)
                       decode_cjr_insn("jr      ");
                   else
                       decode_cmv_insn("mv      ");
        INSN_CADD: if (rvfi_insn[11:2] == 10'h0)
                       decode_mnemonic("ebreak  ");
                   else if (rvfi_insn[6:2] == 5'b0)
                       decode_cjr_insn("jalr    ");
                   else
                        decode_cr_insn("add     ");
        INSN_SWSP:  decode_cstore_insn("sw      ");
        default:       decode_mnemonic("INVALID ");
      endcase
    end else begin
      insn_is_compressed = 0;
      unique casez (rvfi_insn)
        // Regular opcodes
        INSN_LUI:        decode_u_insn("lui     ");
        INSN_AUIPC:      decode_u_insn("auipc   ");
        INSN_JAL:   if (rvfi_insn[11:7] == 5'h0)     
                         decode_j_insn("j       ");
                    else
                         decode_j_insn("jal     ");
        INSN_JALR:  if (rvfi_insn[11:7] == 5'h0)
                    decode_i_jalr_insn("jr      ");
                    else
                    decode_i_jalr_insn("jalr    ");
        // BRANCH
        INSN_BEQ:        decode_b_insn("beq     ");
        INSN_BNE:        decode_b_insn("bne     ");
        INSN_BLT:        decode_b_insn("blt     ");
        INSN_BGE:        decode_b_insn("bge     ");
        INSN_BLTU:       decode_b_insn("bltu    ");
        INSN_BGEU:       decode_b_insn("bgeu    ");
        // OPIMM
        INSN_ADDI:   if ({rvfi_insn[31:15],rvfi_insn[11:7]} == 22'h0)
                       decode_mnemonic("nop     ");
                     else if (rvfi_insn[31:20] == 12'h0)
                        decode_r2_insn("mv      ");
                     else
                         decode_i_insn("addi    ");
        INSN_SLTI:       decode_i_insn("slti    ");
        INSN_SLTIU:  decode_i_log_insn("sltiu   ");
        INSN_XORI:   decode_i_log_insn("xori    ");
        INSN_ORI:    decode_i_log_insn("ori     ");
        INSN_ANDI:   decode_i_log_insn("andi    ");
        INSN_SLLI: decode_i_shift_insn("slli    ");
        INSN_SRLI: decode_i_shift_insn("srli    ");
        INSN_SRAI: decode_i_shift_insn("srai    ");
        // OP
        INSN_ADD:        decode_r_insn("add     ");
        INSN_SUB:        decode_r_insn("sub     ");
        INSN_SLL:        decode_r_insn("sll     ");
        INSN_SLT:        decode_r_insn("slt     ");
        INSN_SLTU:       decode_r_insn("sltu    ");
        INSN_XOR:        decode_r_insn("xor     ");
        INSN_SRL:        decode_r_insn("srl     ");
        INSN_SRA:        decode_r_insn("sra     ");
        INSN_OR:         decode_r_insn("or      ");
        INSN_AND:        decode_r_insn("and     ");
        // SYSTEM (CSR manipulation)
        INSN_CSRRW:    decode_csr_insn("csrrw   ");
        INSN_CSRRS:    decode_csr_insn("csrrs   ");
        INSN_CSRRC:    decode_csr_insn("csrrc   ");
        INSN_CSRRWI:   decode_csr_insn("csrrwi  ");
        INSN_CSRRSI:   decode_csr_insn("csrrsi  ");
        INSN_CSRRCI:   decode_csr_insn("csrrci  ");
        // SYSTEM (others)
        INSN_ECALL:    decode_mnemonic("ecall   ");
        INSN_EBREAK:   decode_mnemonic("ebreak  ");
        INSN_MRET:     decode_mnemonic("mret    ");
        INSN_DRET:     decode_mnemonic("dret    ");
        INSN_WFI:      decode_mnemonic("wfi     ");
        // RV32M
        INSN_MUL:        decode_r_insn("mul     ");
        INSN_MUH:        decode_r_insn("mulh    ");
        INSN_MULHSU:     decode_r_insn("mulhsu  ");
        INSN_MULHU:      decode_r_insn("mulhu   ");
        INSN_DIV:        decode_r_insn("div     ");
        INSN_DIVU:       decode_r_insn("divu    ");
        INSN_REM:        decode_r_insn("rem     ");
        INSN_REMU:       decode_r_insn("remu    ");
        // LOAD & STORE
        INSN_LB:      decode_load_insn("lb      ");
        INSN_LH:      decode_load_insn("lh      ");
        INSN_LW:      decode_load_insn("lw      ");
        INSN_LBU:     decode_load_insn("lbu     ");
        INSN_LHU:     decode_load_insn("lhu     ");
        INSN_SB:     decode_store_insn("sb      ");
        INSN_SH:     decode_store_insn("sh      ");
        INSN_SW:     decode_store_insn("sw      ");
        // MISC-MEM
        INSN_FENCE:       decode_fence("fence   ");
        INSN_FENCEI:   decode_mnemonic("fence.i ");
        // RV32B
        INSN_SLOI: decode_i_shift_insn("sloi    ");
        INSN_SROI: decode_i_shift_insn("sroi    ");
        INSN_RORI: decode_i_shift_insn("rori    ");
        INSN_SLO:        decode_r_insn("slo     ");
        INSN_SRO:        decode_r_insn("sro     ");
        INSN_ROL:        decode_r_insn("rol     ");
        INSN_ROR:        decode_r_insn("ror     ");
        INSN_MIN:        decode_r_insn("min     ");
        INSN_MAX:        decode_r_insn("max     ");
        INSN_MINU:       decode_r_insn("minu    ");
        INSN_MAXU:       decode_r_insn("maxu    ");
        INSN_XNOR:       decode_r_insn("xnor    ");
        INSN_ORN:        decode_r_insn("orn     ");
        INSN_ANDN:       decode_r_insn("andn    ");
        INSN_PACK:       decode_r_insn("pack    ");
        INSN_PACKH:      decode_r_insn("packh   ");
        INSN_PACKU:      decode_r_insn("packu   ");
        INSN_ORCB:       decode_r_insn("orcb    ");
        INSN_CLZ:       decode_r2_insn("clz     ");
        INSN_CTZ:       decode_r2_insn("ctz     ");
        INSN_PCNT:      decode_r2_insn("pcnt    ");
        INSN_REV:       decode_r2_insn("rev     ");
        INSN_REV8:      decode_r2_insn("rev8    ");
        // TERNARY BITMABIP INSTR
        INSN_CMIX:     decode_r4c_insn("cmix    ");
        INSN_CMOV:     decode_r4c_insn("cmov    ");
        INSN_FSR:     decode_r4fs_insn("fsr     ");
        INSN_FSL:     decode_r4fs_insn("fsl     ");
        INSN_FSRI:    decode_i_fs_insn("fsri    ");
        default:       decode_mnemonic("INVALID ");
      endcase
    end
  end

endmodule
