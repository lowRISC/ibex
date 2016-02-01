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


`include "riscv_defines.sv"

module riscv_tracer
(
  // Clock and Reset
  input  logic        clk,
  input  logic        rst_n,

  input  logic [4:0]  core_id,

  input  logic [31:0] pc,
  input  logic [31:0] instr,
  input  logic        compressed,
  input  logic        id_valid,
  input  logic        is_decoding,
  input  logic        pipe_flush,

  input  logic [31:0] rs1_value,
  input  logic [31:0] rs2_value,
  input  logic [31:0] rs3_value,

  input  logic [31:0] imm_u_type,
  input  logic [31:0] imm_uj_type,
  input  logic [31:0] imm_i_type,
  input  logic [31:0] imm_iz_type,
  input  logic [31:0] imm_z_type,
  input  logic [31:0] imm_s_type,
  input  logic [31:0] imm_sb_type

);

  integer      f;
  string       fn;
  integer      cycles;
  logic  [4:0] rd, rs1, rs2, rs3;
  logic [31:0] imm;

  typedef struct {
    logic [4: 0] id;
    logic [31:0] value;
  } reg_t;

  typedef struct {
    time         simtime;
    integer      cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    string       mnemonic;
    reg_t        regs[$];
  } instr_trace_t;

  instr_trace_t queue[$];

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
    #1 // delay needed for valid core_id
    $sformat(fn, "trace_core_%h.log", core_id);
    $display("[TRACER] Output filename is: %s", fn);
    f = $fopen(fn, "w");
    $fwrite(f, "%20s\t%6s\t%10s\t%10s\t \t%s\n", "Time", "Cycles", "PC", "Instr", "Mnemonic");
  end

  final
  begin
    $fclose(f);
  end

  // actual tracing
  always @(negedge clk)
  begin
    instr_trace_t trace;

    if (queue.size() > 0) begin
      trace = queue.pop_front();

      $fwrite(f, "%t\t%6d\t0x%h\t0x%h\t%-30s", trace.simtime,
                                            trace.cycles,
                                            trace.pc,
                                            trace.instr,
                                            trace.mnemonic);

      foreach(trace.regs[i])
        $fwrite(f, "  x%0d =%08x", trace.regs[i].id, trace.regs[i].value);

      $fwrite(f, "\n");
    end
  end

  instr_trace_t trace;
  // log execution
  always @(posedge clk)
  begin

    // special case for WFI because we don't wait for unstalling there
    if ((id_valid && is_decoding) || pipe_flush)
    begin
      trace.simtime  = $time;
      trace.cycles   = cycles;
      trace.pc       = pc;
      trace.instr    = instr;
      trace.mnemonic = "sdf";
      trace.regs     = {};

      // get register values
      rd         = instr[`REG_D];
      rs1        = instr[`REG_S1];
      rs2        = instr[`REG_S2];
      rs3        = instr[`REG_S3];

      imm = 0;

      // use casex instead of case inside due to ModelSim bug
      casex (instr)
        // Aliases
        32'h00_00_00_13:   trace.mnemonic = printMnemonic("nop");
        // Regular opcodes
        `INSTR_LUI:        trace.mnemonic = printUInstr("lui");
        `INSTR_AUIPC:      trace.mnemonic = printUInstr("auipc");
        `INSTR_JAL:        trace.mnemonic = printUJInstr("jal");
        `INSTR_JALR:       trace.mnemonic = printIInstr("jalr");
        // BRANCH
        `INSTR_BEQ:        trace.mnemonic = printSBInstr("beq");
        `INSTR_BNE:        trace.mnemonic = printSBInstr("bne");
        `INSTR_BLT:        trace.mnemonic = printSBInstr("blt");
        `INSTR_BGE:        trace.mnemonic = printSBInstr("bge");
        `INSTR_BLTU:       trace.mnemonic = printSBInstr("bltu");
        `INSTR_BGEU:       trace.mnemonic = printSBInstr("bgeu");
        // OPIMM
        `INSTR_ADDI:       trace.mnemonic = printIInstr("addi");
        `INSTR_SLTI:       trace.mnemonic = printIInstr("slti");
        `INSTR_SLTIU:      trace.mnemonic = printIInstr("sltiu");
        `INSTR_XORI:       trace.mnemonic = printIInstr("xori");
        `INSTR_ORI:        trace.mnemonic = printIInstr("ori");
        `INSTR_ANDI:       trace.mnemonic = printIInstr("andi");
        `INSTR_SLLI:       trace.mnemonic = printIInstr("slli");
        `INSTR_SRLI:       trace.mnemonic = printIInstr("srli");
        `INSTR_SRAI:       trace.mnemonic = printIInstr("srai");
        // OP
        `INSTR_ADD:        trace.mnemonic = printRInstr("add");
        `INSTR_SUB:        trace.mnemonic = printRInstr("sub");
        `INSTR_SLL:        trace.mnemonic = printRInstr("sll");
        `INSTR_SLT:        trace.mnemonic = printRInstr("slt");
        `INSTR_SLTU:       trace.mnemonic = printRInstr("sltu");
        `INSTR_XOR:        trace.mnemonic = printRInstr("xor");
        `INSTR_SRL:        trace.mnemonic = printRInstr("srl");
        `INSTR_SRA:        trace.mnemonic = printRInstr("sra");
        `INSTR_OR:         trace.mnemonic = printRInstr("or");
        `INSTR_AND:        trace.mnemonic = printRInstr("and");
        `INSTR_EXTHS:      trace.mnemonic = printRInstr("exths");
        `INSTR_EXTHZ:      trace.mnemonic = printRInstr("exthz");
        `INSTR_EXTBS:      trace.mnemonic = printRInstr("extbs");
        `INSTR_EXTBZ:      trace.mnemonic = printRInstr("extbz");
        // FENCE
        `INSTR_FENCE:      trace.mnemonic = printMnemonic("fence");
        `INSTR_FENCEI:     trace.mnemonic = printMnemonic("fencei");
        // SYSTEM (CSR manipulation)
        `INSTR_CSRRW:      trace.mnemonic = printCSRInstr("CSRRW");
        `INSTR_CSRRS:      trace.mnemonic = printCSRInstr("CSRRS");
        `INSTR_CSRRC:      trace.mnemonic = printCSRInstr("CSRRC");
        `INSTR_CSRRWI:     trace.mnemonic = printCSRInstr("CSRRWI");
        `INSTR_CSRRSI:     trace.mnemonic = printCSRInstr("CSRRSI");
        `INSTR_CSRRCI:     trace.mnemonic = printCSRInstr("CSRRCI");
        // SYSTEM (others)
        `INSTR_ECALL:      trace.mnemonic = printMnemonic("ecall");
        `INSTR_EBREAK:     trace.mnemonic = printMnemonic("ebreak");
        `INSTR_ERET:       trace.mnemonic = printMnemonic("eret");
        `INSTR_WFI:        trace.mnemonic = printMnemonic("wfi");
        // PULP MULTIPLIER
        `INSTR_PMUL:       trace.mnemonic = printRInstr("p.mul");
        `INSTR_PMAC:       trace.mnemonic = printRInstr("p.mac");
        // opcodes with custom decoding
        {25'b?, `OPCODE_LOAD}:       trace.mnemonic = printLoadInstr();
        {25'b?, `OPCODE_LOAD_POST}:  trace.mnemonic = printLoadInstr();
        {25'b?, `OPCODE_STORE}:      trace.mnemonic = printStoreInstr();
        {25'b?, `OPCODE_STORE_POST}: trace.mnemonic = printStoreInstr();
        {25'b?, `OPCODE_HWLOOP}:     trace.mnemonic = printHwloopInstr();
        default:           trace.mnemonic = printMnemonic("INVALID");
      endcase // unique case (instr)

      queue.push_back(trace);
    end
  end // always @ (posedge clk)

  function string printMnemonic(input string mnemonic);
    begin
      return mnemonic;
    end
  endfunction // printMnemonic

  function string printUInstr(input string mnemonic);
    begin
      return $sformatf("%-10s x%0d, 0x%h", mnemonic, rd, imm_u_type);
    end
  endfunction // printUInstr

  function string printRInstr(input string mnemonic);
    begin
      riscv_tracer.trace.regs.push_back({rs1, rs1_value});
      riscv_tracer.trace.regs.push_back({rs2, rs2_value});
      return $sformatf("%-10s x%0d, x%0d, x%0d", mnemonic,
                rd, rs1, rs2);
    end
  endfunction // printRInstr

  function string printIInstr(input string mnemonic);
    begin
      riscv_tracer.trace.regs.push_back({rs1, rs1_value});
      return $sformatf("%-10s x%0d, x%0d, 0x%0h", mnemonic,
                rd, rs1, imm_i_type);
    end
  endfunction // printIInstr

  function string printSBInstr(input string mnemonic);
    begin
      riscv_tracer.trace.regs.push_back({rs1, rs1_value});
      riscv_tracer.trace.regs.push_back({rs2, rs2_value});
      return $sformatf("%-10s x%0d, x%0d, 0x%0h (-> 0x%h)", mnemonic,
                rs1, rs2, imm_sb_type, imm_sb_type + pc);
    end
  endfunction // printSBInstr

  function string printUJInstr(input string mnemonic);
    begin
      return $sformatf("%-10s x%0d, 0x%h (-> 0x%h)", mnemonic, rd, imm_uj_type, imm_uj_type + pc);
    end
  endfunction // printUJInstr

  function string printCSRInstr(input string mnemonic);
    logic [11:0] csr;
    begin
      csr = instr[31:20];

      if (instr[14] == 1'b0) begin
        riscv_tracer.trace.regs.push_back({rs1, rs1_value});
        return $sformatf("%-10s x%0d, 0x%h, x%0d", mnemonic, rd, csr, rs1);
      end else begin
        return $sformatf("%-10s x%0d, 0x%h, 0x%h", mnemonic, rd, csr, imm_z_type);
      end
    end
  endfunction // printCSRInstr

  function string printLoadInstr();
    string str;
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
        3'b011,
        3'b110,
        3'b111: begin
          return printMnemonic("INVALID");
        end
      endcase

      if (instr[14:12] != 3'b111) begin
        // regular load
        if (instr[6:0] != `OPCODE_LOAD_POST) begin
          str = $sformatf("%-10s x%0d, %0d(x%0d)", mnemonic, rd, imm_s_type, rs1);
          riscv_tracer.trace.regs.push_back({rs1, rs1_value});
        end else begin
          str = $sformatf("p.%-8s x%0d, %0d(x%0d!)", mnemonic, rd, imm_s_type, rs1);
          riscv_tracer.trace.regs.push_back({rs1, rs1_value});
        end
      end else begin
        // reg-reg load
        if (instr[6:0] != `OPCODE_LOAD_POST) begin
          str = $sformatf("%-8s x%0d, x%0d(x%0d)", mnemonic, rd, rs2, rs1);
          riscv_tracer.trace.regs.push_back({rs2, rs2_value});
          riscv_tracer.trace.regs.push_back({rs1, rs1_value});
        end else begin
          str = $sformatf("p.%-8s x%0d, x%0d(x%0d!)", mnemonic, rd, rs2, rs1);
          riscv_tracer.trace.regs.push_back({rs2, rs2_value});
          riscv_tracer.trace.regs.push_back({rs1, rs1_value});
        end
      end

      return str;
    end
  endfunction

  function string printStoreInstr();
    string mnemonic;
    string str;
    begin
      case (instr[13:12])
        2'b00:  mnemonic = "sb";
        2'b01:  mnemonic = "sh";
        2'b10:  mnemonic = "sw";
        2'b11: begin
          return printMnemonic("INVALID");
        end
      endcase

      if (instr[14] == 1'b0) begin
        // regular store
        if (instr[6:0] != `OPCODE_STORE_POST) begin
          str = $sformatf("%-10s x%0d, %0d(x%0d)", mnemonic, rs2, imm_s_type, rs1);
          riscv_tracer.trace.regs.push_back({rs2, rs2_value});
          riscv_tracer.trace.regs.push_back({rs1, rs1_value});
        end else begin
          str = $sformatf("p.%-8s x%0d, %0d(x%0d!)", mnemonic, rs2, imm_s_type, rs1);
          riscv_tracer.trace.regs.push_back({rs2, rs2_value});
          riscv_tracer.trace.regs.push_back({rs1, rs1_value});
        end
      end else begin
        // reg-reg store
        if (instr[6:0] != `OPCODE_STORE_POST) begin
          str = $sformatf("p.%-8s x%0d, x%0d(x%0d)", mnemonic, rs2, rs3, rs1);
          riscv_tracer.trace.regs.push_back({rs2, rs2_value});
          riscv_tracer.trace.regs.push_back({rs3, rs3_value});
          riscv_tracer.trace.regs.push_back({rs1, rs1_value});
        end else begin
          str = $sformatf("p.%-8s x%0d, x%0d(x%0d!)", mnemonic, rs2, rs3, rs1);
          riscv_tracer.trace.regs.push_back({rs2, rs2_value});
          riscv_tracer.trace.regs.push_back({rs3, rs3_value});
          riscv_tracer.trace.regs.push_back({rs1, rs1_value});
        end
      end

      return str;
    end
  endfunction // printSInstr

  function string printHwloopInstr();
    string str;
    string mnemonic;
    begin
      // set mnemonic
      case (instr[14:12])
        3'b000: mnemonic = "LSTARTI";
        3'b001: mnemonic = "LENDI";
        3'b010: mnemonic = "LCOUNT";
        3'b011: mnemonic = "LCOUNTI";
        3'b100: mnemonic = "LSETUP";
        3'b101: mnemonic = "LSETUPI";
        3'b111: begin
          return printMnemonic("INVALID");
        end
      endcase

      // decode and print instruction
      case (instr[14:12])
        // lp.starti and lp.endi
        3'b000,
        3'b001: str = $sformatf("%-10s x%0d, 0x%h (-> 0x%h)", mnemonic, rd, imm_iz_type, pc + (imm_iz_type << 1));
        // lp.count
        3'b010: str = $sformatf("%-10s x%0d, x%0d (0x%h)", mnemonic, rd, rs1, rs1_value);
        // lp.counti
        3'b011: str = $sformatf("%-10s x%0d, 0x%h", mnemonic, rd, imm_iz_type);
        // lp.setup
        3'b100: str = $sformatf("%-10s x%0d, x%0d (0x%h), 0x%h (-> 0x%h)", mnemonic,
                           rd, rs1, rs1_value, imm_iz_type, pc + (imm_iz_type << 1));
        // lp.setupi
        3'b101: str = $sformatf("%-10s x%0d, x%0d (0x%h), 0x%h (-> 0x%h)", mnemonic,
                          rd, rs1, rs1_value, imm_iz_type, pc + (imm_z_type << 1));
      endcase

      return str;
    end
  endfunction

endmodule

