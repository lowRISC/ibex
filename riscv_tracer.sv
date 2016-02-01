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
  string       mnemonic;

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

  // log execution
  always @(posedge clk)
  begin
    // get register values
    rd         = instr[`REG_D];
    rs1        = instr[`REG_S1];
    rs2        = instr[`REG_S2];
    rs3        = instr[`REG_S3];

    // special case for WFI because we don't wait for unstalling there
    if ((id_valid && is_decoding) || pipe_flush)
    begin
      mnemonic = "";
      imm = 0;

      $fwrite(f, "%t\t%6d\t0x%h\t", $time, cycles, pc);
      $fwrite(f, "0x%h\tI\t", instr);

      // use casex instead of case inside due to ModelSim bug
      casex (instr)
        // Aliases
        32'h00_00_00_13:   printMnemonic("NOP");
        // Regular opcodes
        // `INSTR_CUSTOM0:    printMnemonic("CUSTOM0");
        // `INSTR_CUSTOM1:    printMnemonic("CUSTOM1");
        `INSTR_LUI:        printUInstr("LUI");
        `INSTR_AUIPC:      printUInstr("AUIPC");
        `INSTR_JAL:        printUJInstr("JAL");
        `INSTR_JALR:       printIInstr("JALR");
        // BRANCH
        `INSTR_BEQ:        printSBInstr("BEQ");
        `INSTR_BNE:        printSBInstr("BNE");
        `INSTR_BLT:        printSBInstr("BLT");
        `INSTR_BGE:        printSBInstr("BGE");
        `INSTR_BLTU:       printSBInstr("BLTU");
        `INSTR_BGEU:       printSBInstr("BGEU");
        // OPIMM
        `INSTR_ADDI:       printIInstr("ADDI");
        `INSTR_SLTI:       printIInstr("SLTI");
        `INSTR_SLTIU:      printIInstr("SLTIU");
        `INSTR_XORI:       printIInstr("XORI");
        `INSTR_ORI:        printIInstr("ORI");
        `INSTR_ANDI:       printIInstr("ANDI");
        `INSTR_SLLI:       printIInstr("SLLI");
        `INSTR_SRLI:       printIInstr("SRLI");
        `INSTR_SRAI:       printIInstr("SRAI");
        // OP
        `INSTR_ADD:        printRInstr("ADD");
        `INSTR_SUB:        printRInstr("SUB");
        `INSTR_SLL:        printRInstr("SLL");
        `INSTR_SLT:        printRInstr("SLT");
        `INSTR_SLTU:       printRInstr("SLTU");
        `INSTR_XOR:        printRInstr("XOR");
        `INSTR_SRL:        printRInstr("SRL");
        `INSTR_SRA:        printRInstr("SRA");
        `INSTR_OR:         printRInstr("OR");
        `INSTR_AND:        printRInstr("AND");
        `INSTR_EXTHS:      printRInstr("EXTHS");
        `INSTR_EXTHZ:      printRInstr("EXTHZ");
        `INSTR_EXTBS:      printRInstr("EXTBS");
        `INSTR_EXTBZ:      printRInstr("EXTBZ");
        // FENCE
        `INSTR_FENCE:      printMnemonic("FENCE");
        `INSTR_FENCEI:     printMnemonic("FENCEI");
        // SYSTEM (CSR manipulation)
        `INSTR_CSRRW:      printCSRInstr("CSRRW");
        `INSTR_CSRRS:      printCSRInstr("CSRRS");
        `INSTR_CSRRC:      printCSRInstr("CSRRC");
        `INSTR_CSRRWI:     printCSRInstr("CSRRWI");
        `INSTR_CSRRSI:     printCSRInstr("CSRRSI");
        `INSTR_CSRRCI:     printCSRInstr("CSRRCI");
        // SYSTEM (others)
        `INSTR_ECALL:      printMnemonic("ECALL");
        `INSTR_EBREAK:     printMnemonic("EBREAK");
        `INSTR_ERET:       printMnemonic("ERET");
        `INSTR_WFI:        printMnemonic("WFI");
        // PULP MULTIPLIER
        `INSTR_PMUL:       printRInstr("P.MUL");
        `INSTR_PMAC:       printRInstr("P.MAC");
        // opcodes with custom decoding
        {25'b?, `OPCODE_LOAD}:       printLoadInstr();
        {25'b?, `OPCODE_LOAD_POST}:  printLoadInstr();
        {25'b?, `OPCODE_STORE}:      printStoreInstr();
        {25'b?, `OPCODE_STORE_POST}: printStoreInstr();
        {25'b?, `OPCODE_HWLOOP}:     printHwloopInstr();
        default:           printMnemonic("INVALID");
      endcase // unique case (instr)

      $fflush(f);
    end
  end // always @ (posedge clk)

  function void printMnemonic(input string mnemonic);
    begin
      riscv_tracer.mnemonic = mnemonic;
      $fdisplay(f, "%7s", mnemonic);
    end
  endfunction // printMnemonic

  function void printUInstr(input string mnemonic);
    begin
      riscv_tracer.mnemonic = mnemonic;
      imm = imm_u_type;
      $fdisplay(f, "%7s\tx%0d, 0x%h (imm)", mnemonic, rd, imm);
    end
  endfunction // printUInstr

  function void printRInstr(input string mnemonic);
    begin
      riscv_tracer.mnemonic = mnemonic;
      $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), x%0d (0x%h)", mnemonic,
                rd, rs1, rs1_value, rs2, rs2_value);
    end
  endfunction // printRInstr

  function void printR3Instr(input string mnemonic);
    begin
      riscv_tracer.mnemonic = mnemonic;
      $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), x%0d (0x%h), x%0d (0x%h)", mnemonic,
                rd, rs1, rs1_value, rs2, rs2_value, rs3, rs3_value);
    end
  endfunction // printRInstr

  function void printIInstr(input string mnemonic);
    begin
      riscv_tracer.mnemonic = mnemonic;
      imm = imm_i_type;
      $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), 0x%0h (imm)", mnemonic,
                rd, rs1, rs1_value, imm);
    end
  endfunction // printIInstr

  function void printSBInstr(input string mnemonic);
    begin
      riscv_tracer.mnemonic = mnemonic;
      imm = imm_sb_type;
      $fdisplay(f, "%7s\tx%0d (0x%h), x%0d (0x%h), 0x%0h (-> 0x%h)", mnemonic,
                rs1, rs1_value, rs2, rs2_value, imm, imm+pc);
    end
  endfunction // printSBInstr

  function void printUJInstr(input string mnemonic);
    begin
      riscv_tracer.mnemonic = mnemonic;
      imm = imm_uj_type;
      $fdisplay(f, "%7s\tx%0d, 0x%h (-> 0x%h)", mnemonic, rd, imm, imm+pc);
    end
  endfunction // printUJInstr

  function void printCSRInstr(input string mnemonic);
    logic [11:0] csr;
    begin
      riscv_tracer.mnemonic = mnemonic;
      imm = imm_z_type;
      csr = instr[31:20];

      if (instr[14] == 1'b0) begin
        $fdisplay(f, "%7s\tx%0d, 0x%h (csr), x%0d (0x%h)", mnemonic, rd, csr,
          rs1, rs1_value);
      end else begin
        $fdisplay(f, "%7s\tx%0d, 0x%h (csr), 0x%h (imm)", mnemonic, rd, csr, imm);
      end
    end
  endfunction // printCSRInstr

  function void printLoadInstr();
    string mnemonic;
    logic [2:0] size;
    begin
      // detect reg-reg load and find size
      size = instr[14:12];
      if (instr[14:12] == 3'b111)
        size = instr[30:28];
      case (size)
        3'b000: mnemonic = "LB";
        3'b001: mnemonic = "LH";
        3'b010: mnemonic = "LW";
        3'b100: mnemonic = "LBU";
        3'b101: mnemonic = "LHU";
        3'b011,
        3'b110,
        3'b111: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      // compose mnemonic
      if (instr[14:12] == 3'b111)
        mnemonic = {mnemonic, "RR"};
      if (instr[6:0] == `OPCODE_LOAD_POST)
        mnemonic = {mnemonic, "POST"};
      riscv_tracer.mnemonic = mnemonic;

      if (instr[14:12] != 3'b111) begin
        // regular load
        imm = imm_i_type;
        if (instr[6:0] != `OPCODE_LOAD_POST)
          $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), 0x%0h (imm) (-> 0x%h)",
                    mnemonic, rd, rs1, rs1_value, imm, imm+rs1_value);
        else
          $fdisplay(f, "%7s\tx%0d, x%0d! (0x%h), 0x%0h (imm) (-> 0x%h)",
                    mnemonic, rd, rs1, rs1_value, imm, rs1_value);
      end else begin
        // reg-reg load
        if (instr[6:0] != `OPCODE_LOAD_POST)
          $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), x%0d (0x%h) (-> 0x%h)", mnemonic,
                    rd, rs1, rs1_value, rs2, rs2_value, rs1_value+rs2_value);
        else
          $fdisplay(f, "%7s\tx%0d, x%0d! (0x%h), x%0d (0x%h) (-> 0x%h)", mnemonic,
                    rd, rs1, rs1_value, rs2, rs2_value, rs1_value);
      end
    end
  endfunction

  function void printStoreInstr();
    string mnemonic;
    begin
      case (instr[13:12])
        2'b00:  mnemonic = "SB";
        2'b01:  mnemonic = "SH";
        2'b10:  mnemonic = "SW";
        2'b11: begin
          printMnemonic("INVALID");
          return;
        end
      endcase

      // compose mnemonic
      if (instr[14])
        mnemonic = {mnemonic, "RR"};
      if (instr[6:0] == `OPCODE_STORE_POST)
        mnemonic = {mnemonic, "POST"};
      riscv_tracer.mnemonic = mnemonic;

      if (instr[14] == 1'b0) begin
        // regular store
        imm = imm_s_type;
        if (instr[6:0] != `OPCODE_STORE_POST)
          $fdisplay(f, "%7s\tx%0d (0x%h), x%0d (0x%h), 0x%0h (imm) (-> 0x%h)",
                    mnemonic, rs1, rs1_value, rs2, rs2_value, imm, imm+rs1_value);
        else
          $fdisplay(f, "%7s\tx%0d! (0x%h), x%0d (0x%h), 0x%0h (imm) (-> 0x%h)",
                    mnemonic, rs1, rs1_value, rs2, rs2_value, imm, rs1_value);
      end else begin
        // reg-reg store
        if (instr[6:0] != `OPCODE_STORE_POST)
          $fdisplay(f, "%7s\tx%0d (0x%h), x%0d (0x%h), x%0d (0x%h) (-> 0x%h)", mnemonic,
                    rs1, rs1_value, rs2, rs2_value, rs3, rs3_value, rs1_value+rs3_value);
        else
          $fdisplay(f, "%7s\tx%0d! (0x%h), x%0d (0x%h), x%0d (0x%h) (-> 0x%h)", mnemonic,
                    rs1, rs1_value, rs2, rs2_value, rs3, rs3_value, rs1_value);
      end
    end
  endfunction // printSInstr

  function void printHwloopInstr();
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
          printMnemonic("INVALID");
          return;
        end
      endcase
      riscv_tracer.mnemonic = mnemonic;

      // decode and print instruction
      imm = imm_iz_type;
      case (instr[14:12])
        // lp.starti and lp.endi
        3'b000,
        3'b001: $fdisplay(f, "%7s\tx%0d, 0x%h (-> 0x%h)", mnemonic, rd, imm, pc+(imm<<1));
        // lp.count
        3'b010: $fdisplay(f, "%7s\tx%0d, x%0d (0x%h)", mnemonic, rd, rs1, rs1_value);
        // lp.counti
        3'b011: $fdisplay(f, "%7s\tx%0d, 0x%h", mnemonic, rd, imm);
        // lp.setup
        3'b100: $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), 0x%h (-> 0x%h)", mnemonic,
                          rd, rs1, rs1_value, imm, pc+(imm<<1));
        // lp.setupi
        3'b101: $fdisplay(f, "%7s\tx%0d, x%0d (0x%h), 0x%h (-> 0x%h)", mnemonic,
                          rd, rs1, rs1_value, imm, pc+(imm_z_type << 1));
      endcase
    end
  endfunction

endmodule

