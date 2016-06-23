// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
// Design Name:    RISC-V Tracer                                              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Traces the executed instructions                           //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


import riscv_defines::*;
import riscv_tracer_defines::*;

// Source/Destination register instruction index
`define REG_S1 19:15
`define REG_S2 24:20
`define REG_S3 29:25
`define REG_D  11:07

module riscv_tracer
(
  // Clock and Reset
  input  logic        clk,
  input  logic        rst_n,

  input  logic        fetch_enable,
  input  logic [3:0]  core_id,
  input  logic [5:0]  cluster_id,

  input  logic [31:0] pc,
  input  logic [31:0] instr,
  input  logic        compressed,
  input  logic        id_valid,
  input  logic        is_decoding,
  input  logic        pipe_flush,

  input  logic [31:0] rs1_value,
  input  logic [31:0] rs2_value,
  input  logic [31:0] rs3_value,
  input  logic [31:0] rs2_value_vec,

  input  logic        ex_valid,
  input  logic [ 4:0] ex_reg_addr,
  input  logic        ex_reg_we,
  input  logic [31:0] ex_reg_wdata,

  input  logic        ex_data_req,
  input  logic        ex_data_gnt,
  input  logic        ex_data_we,
  input  logic [31:0] ex_data_addr,
  input  logic [31:0] ex_data_wdata,

  input  logic        wb_bypass,

  input  logic        wb_valid,
  input  logic [ 4:0] wb_reg_addr,
  input  logic        wb_reg_we,
  input  logic [31:0] wb_reg_wdata,

  input  logic [31:0] imm_u_type,
  input  logic [31:0] imm_uj_type,
  input  logic [31:0] imm_i_type,
  input  logic [11:0] imm_iz_type,
  input  logic [31:0] imm_z_type,
  input  logic [31:0] imm_s_type,
  input  logic [31:0] imm_sb_type,
  input  logic [31:0] imm_s2_type,
  input  logic [31:0] imm_s3_type,
  input  logic [31:0] imm_vs_type,
  input  logic [31:0] imm_vu_type,
  input  logic [ 4:0] imm_clip_type
);

  integer      f;
  string       fn;
  integer      cycles;
  logic [ 4:0] rd, rs1, rs2, rs3;

  typedef struct {
    logic [ 4:0] addr;
    logic [31:0] value;
  } reg_t;

  typedef struct {
    logic [31:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [31:0] wdata;
    logic [31:0] rdata;
  } mem_acc_t;

  class instr_trace_t;
    time         simtime;
    integer      cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    string       str;
    reg_t        regs_read[$];
    reg_t        regs_write[$];
    mem_acc_t    mem_access[$];

    function new ();
      str        = "";
      regs_read  = {};
      regs_write = {};
      mem_access = {};
    endfunction

    function string regAddrToStr(input logic [4:0] addr);
      begin
        if (addr < 10)
          return $sformatf(" x%0d", addr);
        else
          return $sformatf("x%0d", addr);
      end
    endfunction

    function void printInstrTrace();
      mem_acc_t mem_acc;
      begin
        $fwrite(f, "%t %15d %h %h %-36s", simtime,
                                          cycles,
                                          pc,
                                          instr,
                                          str);

        foreach(regs_write[i]) begin
          if (regs_write[i].addr != 0)
            $fwrite(f, " %s=%08x", regAddrToStr(regs_write[i].addr), regs_write[i].value);
        end

        foreach(regs_read[i]) begin
          if (regs_read[i].addr != 0)
            $fwrite(f, " %s:%08x", regAddrToStr(regs_read[i].addr), regs_read[i].value);
        end

        if (mem_access.size() > 0) begin
          mem_acc = mem_access.pop_front();

          $fwrite(f, "  PA:%08x", mem_acc.addr);
        end

        $fwrite(f, "\n");
      end
    endfunction

    function void printMnemonic(input string mnemonic);
      begin
        str = mnemonic;
      end
    endfunction // printMnemonic

    function void printRInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_read.push_back('{rs2, rs2_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
      end
    endfunction // printRInstr

    function void printAddNInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_read.push_back('{rs2, rs2_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, x%0d, 0x%0d", mnemonic, rd, rs1, rs2, $unsigned(imm_s3_type[4:0]));
      end
    endfunction // printAddNInstr

    function void printR1Instr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d", mnemonic, rd, rs1);
      end
    endfunction // printR1Instr

    function void printR3Instr(input string mnemonic);
      begin
        regs_read.push_back('{rd, rs3_value});
        regs_read.push_back('{rs1, rs1_value});
        regs_read.push_back('{rs2, rs2_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
      end
    endfunction // printR3Instr

    function void printClipInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $unsigned(imm_clip_type));
      end
    endfunction // printRInstr

    function void printIInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $signed(imm_i_type));
      end
    endfunction // printIInstr

    function void printIuInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, rd, rs1, imm_i_type);
      end
    endfunction // printIuInstr

    function void printUInstr(input string mnemonic);
      begin
        regs_write.push_back('{rd, 'x});
        str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, {imm_u_type[31:12], 12'h000});
      end
    endfunction // printUInstr

    function void printUJInstr(input string mnemonic);
      begin
        regs_write.push_back('{rd, 'x});
        str =  $sformatf("%-16s x%0d, %0d", mnemonic, rd, $signed(imm_uj_type));
      end
    endfunction // printUJInstr

    function void printSBInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_read.push_back('{rs2, rs2_value});
        str =  $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rs1, rs2, $signed(imm_sb_type));
      end
    endfunction // printSBInstr

    function void printSBallInstr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        str =  $sformatf("%-16s x%0d, %0d", mnemonic, rs1, $signed(imm_sb_type));
      end
    endfunction // printSBInstr

    function void printCSRInstr(input string mnemonic);
      logic [11:0] csr;
      begin
        csr = instr[31:20];

        regs_write.push_back('{rd, 'x});

        if (instr[14] == 1'b0) begin
          regs_read.push_back('{rs1, rs1_value});
          str = $sformatf("%-16s x%0d, x%0d, 0x%h", mnemonic, rd, rs1, csr);
        end else begin
          str = $sformatf("%-16s x%0d, 0x%h, 0x%h", mnemonic, rd, imm_z_type, csr);
        end
      end
    endfunction // printCSRInstr

    function void printBit1Instr(input string mnemonic);
      begin
        regs_read.push_back('{rs1, rs1_value});
        regs_write.push_back('{rd, 'x});
        str =  $sformatf("%-16s x%0d, x%0d, %0d, %0d", mnemonic, rd, rs1, imm_s3_type, imm_s2_type);
      end
    endfunction

    function void printBit2Instr(input string mnemonic);
      begin
        regs_read.push_back('{rd, rs3_value});
        regs_read.push_back('{rs1, rs1_value});
        regs_write.push_back('{rd, 'x});
        str =  $sformatf("%-16s x%0d, x%0d, %0d, %0d", mnemonic, rd, rs1, imm_s3_type, imm_s2_type);
      end
    endfunction

    function void printLoadInstr();
      string mnemonic;
      logic [2:0] size;
      begin
        // detect reg-reg load and find size
        size = instr[14:12];
        if (instr[14:12] == 3'b111)
          size = instr[30:28];

        case (size)
          3'b000: mnemonic = "lb";
          3'b001: mnemonic = "lh";
          3'b010: mnemonic = "lw";
          3'b100: mnemonic = "lbu";
          3'b101: mnemonic = "lhu";
          3'b110: mnemonic = "p.elw";
          3'b011,
          3'b111: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        regs_write.push_back('{rd, 'x});

        if (instr[14:12] != 3'b111) begin
          // regular load
          if (instr[6:0] != OPCODE_LOAD_POST) begin
            regs_read.push_back('{rs1, rs1_value});
            str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rd, $signed(imm_i_type), rs1);
          end else begin
            regs_read.push_back('{rs1, rs1_value});
            regs_write.push_back('{rs1, 'x});
            str = $sformatf("p.%-14s x%0d, %0d(x%0d!)", mnemonic, rd, $signed(imm_i_type), rs1);
          end
        end else begin
          // reg-reg load
          if (instr[6:0] != OPCODE_LOAD_POST) begin
            regs_read.push_back('{rs2, rs2_value});
            regs_read.push_back('{rs1, rs1_value});
            str = $sformatf("%-16s x%0d, x%0d(x%0d)", mnemonic, rd, rs2, rs1);
          end else begin
            regs_read.push_back('{rs2, rs2_value});
            regs_read.push_back('{rs1, rs1_value});
            regs_write.push_back('{rs1, 'x});
            str = $sformatf("p.%-14s x%0d, x%0d(x%0d!)", mnemonic, rd, rs2, rs1);
          end
        end
      end
    endfunction

    function void printStoreInstr();
      string mnemonic;
      begin

        case (instr[13:12])
          2'b00:  mnemonic = "sb";
          2'b01:  mnemonic = "sh";
          2'b10:  mnemonic = "sw";
          2'b11: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        if (instr[14] == 1'b0) begin
          // regular store
          if (instr[6:0] != OPCODE_STORE_POST) begin
            regs_read.push_back('{rs2, rs2_value});
            regs_read.push_back('{rs1, rs1_value});
            str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rs2, $signed(imm_s_type), rs1);
          end else begin
            regs_read.push_back('{rs2, rs2_value});
            regs_read.push_back('{rs1, rs1_value});
            regs_write.push_back('{rs1, 'x});
            str = $sformatf("p.%-14s x%0d, %0d(x%0d!)", mnemonic, rs2, $signed(imm_s_type), rs1);
          end
        end else begin
          // reg-reg store
          if (instr[6:0] != OPCODE_STORE_POST) begin
            regs_read.push_back('{rs2, rs2_value});
            regs_read.push_back('{rs3, rs3_value});
            regs_read.push_back('{rs1, rs1_value});
            str = $sformatf("p.%-14s x%0d, x%0d(x%0d)", mnemonic, rs2, rs3, rs1);
          end else begin
            regs_read.push_back('{rs2, rs2_value});
            regs_read.push_back('{rs3, rs3_value});
            regs_read.push_back('{rs1, rs1_value});
            regs_write.push_back('{rs1, 'x});
            str = $sformatf("p.%-14s x%0d, x%0d(x%0d!)", mnemonic, rs2, rs3, rs1);
          end
        end
      end
    endfunction // printSInstr

    function void printHwloopInstr();
      string mnemonic;
      begin
        // set mnemonic
        case (instr[14:12])
          3'b000: mnemonic = "lp.starti";
          3'b001: mnemonic = "lp.endi";
          3'b010: mnemonic = "lp.count";
          3'b011: mnemonic = "lp.counti";
          3'b100: mnemonic = "lp.setup";
          3'b101: mnemonic = "lp.setupi";
          3'b111: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        // decode and print instruction
        case (instr[14:12])
          // lp.starti and lp.endi
          3'b000,
          3'b001: str = $sformatf("%-16s 0x%0d, 0x%0h", mnemonic, rd, imm_iz_type);
          // lp.count
          3'b010: begin
            regs_read.push_back('{rs1, rs1_value});
            str = $sformatf("%-16s 0x%0d, x%0d", mnemonic, rd, rs1);
          end
          // lp.counti
          3'b011: str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, imm_iz_type);
          // lp.setup
          3'b100: begin
            regs_read.push_back('{rs1, rs1_value});
            str = $sformatf("%-16s 0x%0d, x%0d, 0x%0h", mnemonic, rd, rs1, imm_iz_type);
          end
          // lp.setupi
          3'b101: begin
            str = $sformatf("%-16s 0x%0d, 0x%0h, 0x%0h", mnemonic, rd, imm_iz_type, rs1);
          end
        endcase
      end
    endfunction

    function void printMulInstr();
      string mnemonic;
      string str_suf;
      string str_imm;
      string str_asm;
      begin

        // always read rs1 and rs2 and write rd
        regs_read.push_back('{rs1, rs1_value});
        regs_read.push_back('{rs2, rs2_value});
        regs_write.push_back('{rd, 'x});

        if (instr[12])
          regs_read.push_back('{rd, rs3_value});

        case ({instr[31:30], instr[14]})
          3'b000: str_suf = "u";
          3'b001: str_suf = "uR";
          3'b010: str_suf = "hhu";
          3'b011: str_suf = "hhuR";
          3'b100: str_suf = "s";
          3'b101: str_suf = "sR";
          3'b110: str_suf = "hhs";
          3'b111: str_suf = "hhsR";
        endcase

        if (instr[12])
          mnemonic = "p.mac";
        else
          mnemonic = "p.mul";

        if (imm_s3_type[4:0] != 5'b00000)
          str_asm = $sformatf("%s%sN", mnemonic, str_suf);
        else
          str_asm = $sformatf("%s%s", mnemonic, str_suf);

        if (instr[29:25] != 5'b00000)
          str = $sformatf("%-16s x%0d, x%0d, x%0d, %0d", str_asm, rd, rs1, rs2, $unsigned(imm_s3_type[4:0]));
        else
          str = $sformatf("%-16s x%0d, x%0d, x%0d", str_asm, rd, rs1, rs2);
      end
    endfunction

    function void printVecInstr();
      string mnemonic;
      string str_asm;
      string str_args;
      string str_hb;
      string str_sci;
      string str_imm;
      begin

        // always read rs1 and write rd
        regs_read.push_back('{rs1, rs1_value});
        regs_write.push_back('{rd, 'x});

        case (instr[14:13])
          2'b00: str_sci = "";
          2'b10: str_sci = ".sc";
          2'b11: str_sci = ".sci";
        endcase

        if (instr[12])
          str_hb = ".b";
        else
          str_hb = ".h";

        // set mnemonic
        case (instr[31:26])
          6'b000000: begin mnemonic = "pv.add";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000010: begin mnemonic = "pv.sub";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000100: begin mnemonic = "pv.avg";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000110: begin mnemonic = "pv.avgu";     str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b001000: begin mnemonic = "pv.min";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001010: begin mnemonic = "pv.minu";     str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b001100: begin mnemonic = "pv.max";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001110: begin mnemonic = "pv.maxu";     str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b010000: begin mnemonic = "pv.srl";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b010010: begin mnemonic = "pv.sra";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b010100: begin mnemonic = "pv.sll";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b010110: begin mnemonic = "pv.or";       str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b011000: begin mnemonic = "pv.xor";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b011010: begin mnemonic = "pv.and";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b011100: begin mnemonic = "pv.abs";      str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b011110: begin mnemonic = "pv.extract";  str_imm = $sformatf("0x%0d", imm_vs_type); str_sci = ""; end
          6'b100000: begin mnemonic = "pv.extractu"; str_imm = $sformatf("0x%0d", imm_vu_type); str_sci = ""; end
          6'b100010: begin mnemonic = "pv.insert";   str_imm = $sformatf("0x%0d", imm_vs_type); end

          // shuffle/pack
          6'b110000: begin mnemonic = "pv.shuffle";  str_imm = $sformatf("N/A"); end
          6'b110010: begin mnemonic = "pv.shuffle2"; end
          6'b110100: begin mnemonic = "pv.pack";     end
          6'b110110: begin mnemonic = "pv.packhi";   end
          6'b111000: begin mnemonic = "pv.packlo";   end

          // comparisons
          6'b000001: begin mnemonic = "pv.cmpeq";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000011: begin mnemonic = "pv.cmpne";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000101: begin mnemonic = "pv.cmpgt";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b000111: begin mnemonic = "pv.cmpge";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001001: begin mnemonic = "pv.cmplt";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001011: begin mnemonic = "pv.cmple";    str_imm = $sformatf("0x%0d", imm_vs_type); end
          6'b001101: begin mnemonic = "pv.cmpgtu";   str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b001111: begin mnemonic = "pv.cmpgeu";   str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b010001: begin mnemonic = "pv.cmpltu";   str_imm = $sformatf("0x%0d", imm_vu_type); end
          6'b010011: begin mnemonic = "pv.cmpleu";   str_imm = $sformatf("0x%0d", imm_vu_type); end

          default: begin
            printMnemonic("INVALID");
            return;
          end
        endcase

        if (str_sci == "") begin
          regs_read.push_back('{rs2, rs2_value});
          str_args = $sformatf("x%0d, x%0d, x%0d", rd, rs1, rs2);
        end else if (str_sci == ".sc") begin
          regs_read.push_back('{rs2, rs2_value_vec});
          str_args = $sformatf("x%0d, x%0d, x%0d", rd, rs1, rs2);
        end else if (str_sci == ".sci") begin
          str_args = $sformatf("x%0d, x%0d, %s", rd, rs1, str_imm);
        end

        str_asm = $sformatf("%s%s%s", mnemonic, str_sci, str_hb);

        str = $sformatf("%-16s %s", str_asm, str_args);
      end
    endfunction
  endclass

  mailbox #(instr_trace_t) instr_ex = new ();
  mailbox #(instr_trace_t) instr_wb = new ();

  // cycle counter
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
      cycles = 0;
    else
      cycles = cycles + 1;
  end

  // open/close output file for writing
  initial
  begin
    wait(rst_n == 1'b1);
    wait(fetch_enable == 1'b1);
    $sformat(fn, "trace_core_%h_%h.log", cluster_id, core_id);
    $display("[TRACER] Output filename is: %s", fn);
    f = $fopen(fn, "w");
    $fwrite(f, "                Time          Cycles PC       Instr    Mnemonic\n");

  end

  final
  begin
    $fclose(f);
  end

  assign rd  = instr[`REG_D];
  assign rs1 = instr[`REG_S1];
  assign rs2 = instr[`REG_S2];
  assign rs3 = instr[`REG_S3];

  // virtual ID/EX pipeline
  initial
  begin
    instr_trace_t trace;
    mem_acc_t     mem_acc;

    while(1) begin
      instr_ex.get(trace);

      // wait until we are going to the next stage
      do begin
        @(negedge clk);

        // replace register written back
        foreach(trace.regs_write[i])
          if ((trace.regs_write[i].addr == ex_reg_addr) && ex_reg_we)
            trace.regs_write[i].value = ex_reg_wdata;

        // look for data accesses and log them
        if (ex_data_req && ex_data_gnt) begin
          mem_acc.addr = ex_data_addr;
          mem_acc.we   = ex_data_we;

          if (mem_acc.we)
            mem_acc.wdata = ex_data_wdata;
          else
            mem_acc.wdata = 'x;

          trace.mem_access.push_back(mem_acc);
        end
      end while (!ex_valid && !wb_bypass); // ex branches bypass the WB stage

      instr_wb.put(trace);
    end
  end

  // virtual EX/WB pipeline
  initial
  begin
    instr_trace_t trace;

    while(1) begin
      instr_wb.get(trace);

      // wait until we are going to the next stage
      do begin
        @(negedge clk);

        // replace register written back
        foreach(trace.regs_write[i])
          if ((trace.regs_write[i].addr == wb_reg_addr) && wb_reg_we)
            trace.regs_write[i].value = wb_reg_wdata;
      end while (!wb_valid);

      trace.printInstrTrace();
    end
  end

  // log execution
  always @(negedge clk)
  begin
    instr_trace_t trace;

    // special case for WFI because we don't wait for unstalling there
    if ((id_valid && is_decoding) || pipe_flush)
    begin
      trace = new ();

      trace.simtime    = $time;
      trace.cycles     = cycles;
      trace.pc         = pc;
      trace.instr      = instr;

      // use casex instead of case inside due to ModelSim bug
      casex (instr)
        // Aliases
        32'h00_00_00_13:   trace.printMnemonic("nop");
        // Regular opcodes
        INSTR_LUI:        trace.printUInstr("lui");
        INSTR_AUIPC:      trace.printUInstr("auipc");
        INSTR_JAL:        trace.printUJInstr("jal");
        INSTR_JALR:       trace.printIInstr("jalr");
        // BRANCH
        INSTR_BEQ:        trace.printSBInstr("beq");
        INSTR_BNE:        trace.printSBInstr("bne");
        INSTR_BLT:        trace.printSBInstr("blt");
        INSTR_BGE:        trace.printSBInstr("bge");
        INSTR_BLTU:       trace.printSBInstr("bltu");
        INSTR_BGEU:       trace.printSBInstr("bgeu");
        INSTR_BALL:       trace.printSBallInstr("pv.ball");
        // OPIMM
        INSTR_ADDI:       trace.printIInstr("addi");
        INSTR_SLTI:       trace.printIInstr("slti");
        INSTR_SLTIU:      trace.printIInstr("sltiu");
        INSTR_XORI:       trace.printIInstr("xori");
        INSTR_ORI:        trace.printIInstr("ori");
        INSTR_ANDI:       trace.printIInstr("andi");
        INSTR_SLLI:       trace.printIuInstr("slli");
        INSTR_SRLI:       trace.printIuInstr("srli");
        INSTR_SRAI:       trace.printIuInstr("srai");
        // OP
        INSTR_ADD:        trace.printRInstr("add");
        INSTR_SUB:        trace.printRInstr("sub");
        INSTR_SLL:        trace.printRInstr("sll");
        INSTR_SLT:        trace.printRInstr("slt");
        INSTR_SLTU:       trace.printRInstr("sltu");
        INSTR_XOR:        trace.printRInstr("xor");
        INSTR_SRL:        trace.printRInstr("srl");
        INSTR_SRA:        trace.printRInstr("sra");
        INSTR_OR:         trace.printRInstr("or");
        INSTR_AND:        trace.printRInstr("and");
        INSTR_EXTHS:      trace.printRInstr("p.exths");
        INSTR_EXTHZ:      trace.printRInstr("p.exthz");
        INSTR_EXTBS:      trace.printRInstr("p.extbs");
        INSTR_EXTBZ:      trace.printRInstr("p.extbz");
        INSTR_PAVG:       trace.printRInstr("p.avg");
        INSTR_PAVGU:      trace.printRInstr("p.avgu");
        INSTR_PADDN:      trace.printAddNInstr("p.addN");
        INSTR_PADDUN:     trace.printAddNInstr("p.adduN");
        INSTR_PADDRN:     trace.printAddNInstr("p.addRN");
        INSTR_PADDURN:    trace.printAddNInstr("p.adduRN");
        INSTR_PSUBN:      trace.printAddNInstr("p.subN");
        INSTR_PSUBUN:     trace.printAddNInstr("p.subuN");
        INSTR_PSUBRN:     trace.printAddNInstr("p.subRN");
        INSTR_PSUBURN:    trace.printAddNInstr("p.subuRN");
        INSTR_PSLET:      trace.printRInstr("p.slet");
        INSTR_PSLETU:     trace.printRInstr("p.sletu");
        INSTR_PMIN:       trace.printRInstr("p.min");
        INSTR_PMINU:      trace.printRInstr("p.minu");
        INSTR_PMAX:       trace.printRInstr("p.max");
        INSTR_PMAXU:      trace.printRInstr("p.maxu");
        INSTR_PABS:       trace.printR1Instr("p.abs");
        INSTR_PCLIP:      trace.printClipInstr("p.clip");
        INSTR_PCLIPU:     trace.printClipInstr("p.clipu");
        INSTR_PBEXT:      trace.printBit1Instr("p.extract");
        INSTR_PBEXTU:     trace.printBit1Instr("p.extractu");
        INSTR_PBINS:      trace.printBit2Instr("p.insert");
        INSTR_PBCLR:      trace.printBit1Instr("p.bclr");
        INSTR_PBSET:      trace.printBit1Instr("p.bset");
        // FENCE
        INSTR_FENCE:      trace.printMnemonic("fence");
        INSTR_FENCEI:     trace.printMnemonic("fencei");
        // SYSTEM (CSR manipulation)
        INSTR_CSRRW:      trace.printCSRInstr("csrrw");
        INSTR_CSRRS:      trace.printCSRInstr("csrrs");
        INSTR_CSRRC:      trace.printCSRInstr("csrrc");
        INSTR_CSRRWI:     trace.printCSRInstr("csrrwi");
        INSTR_CSRRSI:     trace.printCSRInstr("csrrsi");
        INSTR_CSRRCI:     trace.printCSRInstr("csrrci");
        // SYSTEM (others)
        INSTR_ECALL:      trace.printMnemonic("ecall");
        INSTR_EBREAK:     trace.printMnemonic("ebreak");
        INSTR_ERET:       trace.printMnemonic("eret");
        INSTR_WFI:        trace.printMnemonic("wfi");
        // PULP MULTIPLIER
        INSTR_PMUL:       trace.printRInstr("p.mul");
        INSTR_PMAC:       trace.printR3Instr("p.mac");
        INSTR_DIV:        trace.printRInstr("div");
        INSTR_DIVU:       trace.printRInstr("divu");
        INSTR_REM:        trace.printRInstr("rem");
        INSTR_REMU:       trace.printRInstr("remu");
        // opcodes with custom decoding
        {25'b?, OPCODE_LOAD}:       trace.printLoadInstr();
        {25'b?, OPCODE_LOAD_POST}:  trace.printLoadInstr();
        {25'b?, OPCODE_STORE}:      trace.printStoreInstr();
        {25'b?, OPCODE_STORE_POST}: trace.printStoreInstr();
        {25'b?, OPCODE_HWLOOP}:     trace.printHwloopInstr();
        {25'b?, OPCODE_VECOP}:      trace.printVecInstr();
        INSTR_PMULRN:               trace.printMulInstr();
        default:           trace.printMnemonic("INVALID");
      endcase // unique case (instr)

      instr_ex.put(trace);
    end
  end // always @ (posedge clk)

endmodule
