// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Traces the executed instructions
 */
module ibex_tracer #(
    parameter int unsigned RegAddrWidth = 5
) (
    // Clock and Reset
    input  logic                      clk_i,
    input  logic                      rst_ni,

    input  logic                      fetch_enable_i,
    input  logic [31:0]               hart_id_i,

    input  logic                      valid_i,
    input  logic [31:0]               pc_i,
    input  logic [31:0]               instr_i,
    input  logic [31:0]               rs1_value_i,
    input  logic [31:0]               rs2_value_i,
    input  logic [(RegAddrWidth-1):0] ex_reg_addr_i,
    input  logic [31:0]               ex_reg_wdata_i,
    input  logic [31:0]               ex_data_addr_i,
    input  logic [31:0]               ex_data_wdata_i,
    input  logic [31:0]               ex_data_rdata_i
);

  import ibex_pkg::*;
  import ibex_tracer_pkg::*;

  int          file_handle;
  string       file_name;

  logic [ 4:0] rd, rs1, rs2, rs3;

  typedef struct packed {
    logic [(RegAddrWidth-1):0] addr;
    logic [31:0] value;
  } reg_t;

  typedef struct packed {
    logic        valid;
    logic [31:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [31:0] wdata;
    logic [31:0] rdata;
  } mem_acc_t;

  integer      cycles;
  logic [31:0] pc;
  logic [31:0] instr;
  string       str;
  reg_t        regs_read[3];
  reg_t        regs_write[3];
  mem_acc_t    mem_access[3];

  function void init();
    str        = "";
    for (int i = 0; i < 3; i++) begin
      regs_read[i].addr   = {{RegAddrWidth{1'b0}}};
      regs_read[i].value  = 32'h0;
      regs_write[i].addr  = {{RegAddrWidth{1'b0}}};
      regs_write[i].value = 32'h0;
      mem_access[i].valid = 1'b0;
      mem_access[i].addr  = 32'h0;
      mem_access[i].we    = 1'b0;
      mem_access[i].be    = 4'h0;
      mem_access[i].wdata = 32'h0;
      mem_access[i].rdata = 32'h0;
    end
    rd  = instr_i[11:7];
    rs1 = instr_i[19:15];
    rs2 = instr_i[24:20];
    rs3 = instr_i[29:25];
  endfunction

  function string reg_addr_to_str(input logic [(RegAddrWidth-1):0] addr);
    begin
      if (addr < 10) begin
        return $sformatf(" x%0d", addr);
      end else begin
        return $sformatf("x%0d", addr);
      end
    end
  endfunction

  function void dump_printbuffer_to_file();
    begin
      if (file_handle == 32'h0) begin
        $sformat(file_name, "trace_core_%h.log", hart_id_i);
        $display("[TRACER] Output filename is: %s", file_name);
        file_handle = $fopen(file_name, "w");
        $fwrite(file_handle, "                Time          Cycles PC       Instr    Mnemonic\n");
      end

      $fwrite(file_handle, "%t %15d %h %h %s", $time,
                                        cycles,
                                        pc_i,
                                        instr_i,
                                        str);

      foreach (regs_write[i]) begin
        if (regs_write[i].addr != 0) begin
          $fwrite(file_handle, " %s=0x%08x",
                                 reg_addr_to_str(regs_write[i].addr), regs_write[i].value);
        end
      end

      foreach (regs_read[i]) begin
        if (regs_read[i].addr != 0) begin
          $fwrite(file_handle, " %s:0x%08x",
                                 reg_addr_to_str(regs_read[i].addr), regs_read[i].value);
        end
      end

      foreach (mem_access[i]) begin
        if (mem_access[i].valid) begin
          $fwrite(file_handle, " PA:0x%08x", mem_access[i].addr);

          if (mem_access[i].we == 1'b1) begin
            $fwrite(file_handle, " store:0x%08x", mem_access[i].wdata);
          end else begin
            $fwrite(file_handle, "  load:0x%08x", mem_access[i].rdata);
          end
        end
      end

      $fwrite(file_handle, "\n");
    end
  endfunction

  function void regs_read_push_back(input logic [1:0] idx, input logic [(RegAddrWidth-1):0] addr,
                                    input logic [31:0] value);
    begin
      regs_read[idx].addr  = addr;
      regs_read[idx].value = value;
    end
  endfunction

  function void regs_write_push_back(input logic [1:0] idx, input logic [(RegAddrWidth-1):0] addr,
                                     input logic [31:0] value);
    begin
      regs_write[idx].addr  = addr;
      regs_write[idx].value = value;
    end
  endfunction

  function void mem_access_push_back(input logic [1:0] idx, input logic [31:0] addr,
                                     input logic we = 1'b0, input logic [3:0] be = 4'h0,
                                     input logic [31:0] wdata = 'x, input logic [31:0] rdata = 'x);
    begin
      mem_access[idx].valid = 1'b1;
      mem_access[idx].addr  = addr;
      mem_access[idx].we    = we;
      mem_access[idx].be    = be;
      mem_access[idx].wdata = wdata;
      mem_access[idx].rdata = rdata;
    end
  endfunction

  function void print_mnemonic(input string mnemonic);
    begin
      str = mnemonic;
    end
  endfunction

  function void print_r_instr(input string mnemonic);
    begin
      regs_read_push_back(2'b00, rs1, rs1_value_i);
      regs_read_push_back(2'b01, rs2, rs2_value_i);
      regs_write_push_back(2'b00, rd, 'x);
      str = $sformatf("%s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
    end
  endfunction

  function void print_i_instr(input string mnemonic);
    begin
      regs_read_push_back(2'b00, rs1, rs1_value_i);
      regs_write_push_back(2'b00, rd, 'x);
      str = $sformatf("%s x%0d, x%0d, %0d", mnemonic, rd, rs1,
                       $signed({{20 {instr[31]}}, instr[31:20]}));
    end
  endfunction

  function void print_u_instr(input string mnemonic);
    begin
      regs_write_push_back(2'b00, rd, 'x);
      str = $sformatf("%s x%0d, 0x%0h", mnemonic, rd, {instr[31:12], 12'h000});
    end
  endfunction

  function void print_j_instr(input string mnemonic);
    begin
      regs_write_push_back(2'b00, rd, 'x);
      str =  $sformatf("%s x%0d, %0d", mnemonic, rd,
                        $signed({ {12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0 }));
    end
  endfunction

  function void print_b_instr(input string mnemonic);
    begin
      regs_read_push_back(2'b00, rs1, rs1_value_i);
      regs_read_push_back(2'b01, rs2, rs2_value_i);
      str =  $sformatf("%s x%0d, x%0d, %0d", mnemonic, rs1, rs2,
                        $signed({ {19 {instr[31]}}, instr[31], instr[7], instr[30:25],
                                  instr[11:8], 1'b0 }));
    end
  endfunction

  function void print_csr_instr(input string mnemonic);
    logic [11:0] csr;
    begin
      csr = instr_i[31:20];

      regs_write_push_back(2'b00, rd, 'x);

      if (!instr_i[14]) begin
        regs_read_push_back(2'b00, rs1, rs1_value_i);
        str = $sformatf("%s x%0d, x%0d, 0x%h", mnemonic, rd, rs1, csr);
      end else begin
        str = $sformatf("%s x%0d, 0x%h, 0x%h", mnemonic, rd, { 27'b0, instr[19:15] }, csr);
      end
    end
  endfunction

  function void print_cr_instr(input string mnemonic);
    begin
      rs1 = instr_i[11:7];
      rs2 = instr_i[6:2];

      if (rs2 == 5'b0) begin
        regs_read_push_back(2'b00, rs1, rs1_value_i);
        str = $sformatf("%s x%0d", mnemonic, rs1);
      end else begin
        regs_write_push_back(2'b00, rs1, 'x);
        regs_read_push_back(2'b00, rs2, rs2_value_i);
        str = $sformatf("%s x%0d, x%0d", mnemonic, rs1, rs2);
      end
    end
  endfunction

  function void print_ci_instr(input string mnemonic);
    begin
      regs_write_push_back(2'b00, rd, 'x);
      str = $sformatf("%s x%0d, 0x%h", mnemonic, rd, {instr_i[12], instr_i[4:0]});
    end
  endfunction

  function void print_ciw_instr(input string mnemonic);
    begin
      rd = {2'b01, instr_i[4:2]};
      regs_write_push_back(2'b00, rd, 'x);
      str = $sformatf("%s x%0d, 0x%h", mnemonic, rd,
                      {instr_i[10:7], instr_i[12:11], instr_i[5], instr_i[6]});
    end
  endfunction

  function void print_cb_instr(input string mnemonic);
    logic [8:1] imm;
    begin
      rs1 = {2'b01, instr_i[9:7]};
      if ((instr_i[15:13] == 3'b110) || (instr_i[15:13] == 3'b111)) begin
        imm = {instr_i[12], instr_i[6:5], instr_i[2], instr_i[11:10], instr_i[4:3]};
        regs_read_push_back(2'b00, rs1, rs1_value_i);
      end else begin
        imm = {instr_i[12], instr_i[6:2], 2'b00};
        regs_write_push_back(2'b00, rs1, 'x);
      end
      str = $sformatf("%s x%0d, 0x%h", mnemonic, rs1, imm);
    end
  endfunction

  function void print_cs_instr(input string mnemonic);
    begin
      rd  = {2'b01, instr_i[9:7]};
      rs2 = {2'b01, instr_i[4:2]};

      regs_write_push_back(2'b00, rd, 'x);
      regs_read_push_back(2'b00, rs2, rs2_value_i);
      str = $sformatf("%s x%0d, x%0d", mnemonic, rd, rs2);
    end
  endfunction

  function void print_cj_instr(input string mnemonic);
    logic [11:1] imm;
    imm = {instr_i[12], instr_i[8], instr_i[10:9], instr_i[6],
           instr_i[7], instr[2], instr[11], instr_i[5:3]};
    begin
      str = $sformatf("%s 0x%h", mnemonic, imm);
    end
  endfunction

  function void print_compressed_load_instr(input string mnemonic);
    logic [7:0] imm;
    begin
      // Detect C.LW intruction
      if (instr_i[1:0] == OPCODE_C0) begin
        rd = {2'b01, instr_i[4:2]};
        rs1 = {2'b01, instr_i[9:7]};
        imm = {1'b0, instr[5], instr[12:10], instr[6], 2'b00};
      end else begin
        // LWSP instruction
        rd = instr_i[11:7];
        rs1 = 5'h2;
        imm = {instr[3:2], instr[12], instr[6:4], 2'b00};
      end
      regs_write_push_back(2'b00, rd, 'x);
      regs_read_push_back(2'b00, rs1, rs1_value_i);
      str = $sformatf("%s x%0d, %0d(x%0d)", mnemonic, rd, rs1, imm);
      mem_access_push_back(2'b00, .addr(ex_data_addr_i), .rdata(ex_data_rdata_i));
    end
  endfunction

  function void print_compressed_store_instr(input string mnemonic);
    logic [7:0] imm;
    begin
      // Detect C.SW instruction
      if (instr_i[1:0] == OPCODE_C0) begin
        rs1 = {2'b01, instr_i[9:7]};
        rs2 = {2'b01, instr_i[4:2]};
        imm = {1'b0, instr[5], instr[12:10], instr[6], 2'b00};
      end else begin
        // SWSP instruction
        rs1 = 5'h2;
        rs2 = instr_i[11:7];
        imm = {instr[8:7], instr[12:9], 2'b00};
      end
      str = $sformatf("%s x%0d, %0d(x%0d)", mnemonic, rs2, rs1, imm);
      regs_read_push_back(2'b00, rs1, rs1_value_i);
      regs_read_push_back(2'b01, rs2, rs2_value_i);
      mem_access_push_back(2'b00, .addr(ex_data_addr_i), .we(1'b1), .wdata(ex_data_wdata_i));
    end
  endfunction

  function void print_load_instr();
    string      mnemonic;
    logic [2:0] size;
    begin
      // detect reg-reg load and find size
      size = instr_i[14:12];
      if (instr_i[14:12] == 3'b111) begin
        size = instr_i[30:28];
      end

      unique case (size)
        3'b000: mnemonic = "lb";
        3'b001: mnemonic = "lh";
        3'b010: mnemonic = "lw";
        3'b100: mnemonic = "lbu";
        3'b101: mnemonic = "lhu";
        3'b110: mnemonic = "p.elw";
        3'b011,
        3'b111: begin
          print_mnemonic("INVALID");
          return;
        end
        default: begin
          print_mnemonic("INVALID");
          return;
        end
      endcase

      regs_write_push_back(2'b00, rd, 'x);

      if (instr_i[14:12] != 3'b111) begin
        // regular load
        regs_read_push_back(2'b00, rs1, rs1_value_i);
        str = $sformatf("%s x%0d, %0d(x%0d)", mnemonic, rd,
                         $signed({{20 {instr[31]}}, instr[31:20]}), rs1);
      end else begin
        print_mnemonic("INVALID");
      end

      mem_access_push_back(2'b00, .addr(ex_data_addr_i), .rdata(ex_data_rdata_i));
    end
  endfunction

  function void print_store_instr();
    string    mnemonic;
    begin

      unique case (instr_i[13:12])
        2'b00:  mnemonic = "sb";
        2'b01:  mnemonic = "sh";
        2'b10:  mnemonic = "sw";
        2'b11: begin
          print_mnemonic("INVALID");
          return;
        end
        default: begin
          print_mnemonic("INVALID");
          return;
        end
      endcase

      if (!instr_i[14]) begin
        // regular store
        regs_read_push_back(2'b00, rs1, rs1_value_i);
        regs_read_push_back(2'b01, rs2, rs2_value_i);
        str = $sformatf("%s x%0d, %0d(x%0d)", mnemonic, rs2,
                          $signed({ {20 {instr[31]}}, instr[31:25], instr[11:7] }), rs1);
      end else begin
        print_mnemonic("INVALID");
      end

      mem_access_push_back(2'b00, .addr(ex_data_addr_i), .we(1'b1), .wdata(ex_data_wdata_i));
    end
  endfunction

  // cycle counter
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cycles <= 0;
    end else begin
      cycles <= cycles + 1;
    end
  end

  // close output file for writing
  final begin
    if (file_handle != 32'h0) begin
      $fclose(file_handle);
    end
  end

  // log execution
  always_ff @(posedge clk_i) begin
    // special case for WFI because we don't wait for unstalling there
    if (valid_i) begin

      init();
      cycles     = cycles;
      pc         = pc_i;
      instr      = instr_i;

      // Check for compressed instructions
      if (instr_i[1:0] != 2'b11) begin
        // Separate case to avoid overlapping decoding
        if ((instr_i[15:13] == 3'b100) && (instr_i[1:0] == 2'b10)) begin
          if (instr_i[12]) begin
            if (instr_i[11:2] == 10'h0) begin
              print_mnemonic("c.ebreak");
            end else if (instr_i[6:2] == 5'b0) begin
              print_cr_instr("c.jalr");
            end else begin
              print_cr_instr("c.add");
            end
          end else begin
            if (instr_i[6:2] == 5'h0) begin
              print_cr_instr("c.jr");
            end else begin
              print_cr_instr("c.mv");
            end
          end
        end else begin
          // use casex instead of case inside due to ModelSim bug
          unique casex (instr_i[15:0])
            // C0 Opcodes
            INSTR_CADDI4SPN:  print_ciw_instr("c.addi4spn");
            INSTR_CLW:        print_compressed_load_instr("c.lw");
            INSTR_CSW:        print_compressed_store_instr("c.sw");
            // C1 Opcodes
            INSTR_CADDI:      print_ci_instr("c.addi");
            INSTR_CJAL:       print_cj_instr("c.jal");
            INSTR_CJ:         print_cj_instr("c.j");
            INSTR_CLI:        print_ci_instr("c.li");
            INSTR_CLUI:       print_ci_instr("c.lui");
            INSTR_CSRLI:      print_cb_instr("c.srli");
            INSTR_CSRAI:      print_cb_instr("c.srai");
            INSTR_CANDI:      print_cb_instr("c.andi");
            INSTR_CSUB:       print_cs_instr("c.sub");
            INSTR_CXOR:       print_cs_instr("c.xor");
            INSTR_COR:        print_cs_instr("c.or");
            INSTR_CAND:       print_cs_instr("c.and");
            INSTR_CBEQZ:      print_cb_instr("c.beqz");
            INSTR_CBNEZ:      print_cb_instr("c.bnez");
            // C2 Opcodes
            INSTR_CSLLI:      print_ci_instr("c.slli");
            INSTR_CLWSP:      print_compressed_load_instr("c.lwsp");
            INSTR_SWSP:       print_compressed_store_instr("c.swsp");
            default:          print_mnemonic("INVALID");
          endcase // unique casex (instr_i)
        end
      end else if (instr_i == 32'h00_00_00_13) begin
        // separate case for 'nop' instruction to avoid overlapping with 'addi'
        print_mnemonic("nop");
      end else begin
        // use casex instead of case inside due to ModelSim bug
        unique casex (instr_i)
          // Regular opcodes
          INSTR_LUI:        print_u_instr("lui");
          INSTR_AUIPC:      print_u_instr("auipc");
          INSTR_JAL:        print_j_instr("jal");
          INSTR_JALR:       print_i_instr("jalr");
          // BRANCH
          INSTR_BEQ:        print_b_instr("beq");
          INSTR_BNE:        print_b_instr("bne");
          INSTR_BLT:        print_b_instr("blt");
          INSTR_BGE:        print_b_instr("bge");
          INSTR_BLTU:       print_b_instr("bltu");
          INSTR_BGEU:       print_b_instr("bgeu");
          // OPIMM
          INSTR_ADDI:       print_i_instr("addi");
          INSTR_SLTI:       print_i_instr("slti");
          INSTR_SLTIU:      print_i_instr("sltiu");
          INSTR_XORI:       print_i_instr("xori");
          INSTR_ORI:        print_i_instr("ori");
          INSTR_ANDI:       print_i_instr("andi");
          INSTR_SLLI:       print_i_instr("slli");
          INSTR_SRLI:       print_i_instr("srli");
          INSTR_SRAI:       print_i_instr("srai");
          // OP
          INSTR_ADD:        print_r_instr("add");
          INSTR_SUB:        print_r_instr("sub");
          INSTR_SLL:        print_r_instr("sll");
          INSTR_SLT:        print_r_instr("slt");
          INSTR_SLTU:       print_r_instr("sltu");
          INSTR_XOR:        print_r_instr("xor");
          INSTR_SRL:        print_r_instr("srl");
          INSTR_SRA:        print_r_instr("sra");
          INSTR_OR:         print_r_instr("or");
          INSTR_AND:        print_r_instr("and");
          // SYSTEM (CSR manipulation)
          INSTR_CSRRW:      print_csr_instr("csrrw");
          INSTR_CSRRS:      print_csr_instr("csrrs");
          INSTR_CSRRC:      print_csr_instr("csrrc");
          INSTR_CSRRWI:     print_csr_instr("csrrwi");
          INSTR_CSRRSI:     print_csr_instr("csrrsi");
          INSTR_CSRRCI:     print_csr_instr("csrrci");
          // SYSTEM (others)
          INSTR_ECALL:      print_mnemonic("ecall");
          INSTR_EBREAK:     print_mnemonic("ebreak");
          INSTR_MRET:       print_mnemonic("mret");
          INSTR_DRET:       print_mnemonic("dret");
          INSTR_WFI:        print_mnemonic("wfi");
          // RV32M
          INSTR_PMUL:       print_r_instr("mul");
          INSTR_PMUH:       print_r_instr("mulh");
          INSTR_PMULHSU:    print_r_instr("mulhsu");
          INSTR_PMULHU:     print_r_instr("mulhu");
          INSTR_DIV:        print_r_instr("div");
          INSTR_DIVU:       print_r_instr("divu");
          INSTR_REM:        print_r_instr("rem");
          INSTR_REMU:       print_r_instr("remu");
          // LOAD & STORE
          INSTR_LOAD:       print_load_instr();
          INSTR_STORE:      print_store_instr();
          // MISC-MEM
          INSTR_FENCE:      print_mnemonic("fence");
          default:          print_mnemonic("INVALID");
        endcase // unique case (instr_i)
      end

      // replace register written back
      foreach (regs_write[i]) begin
        if (regs_write[i].addr == ex_reg_addr_i) begin
          regs_write[i].value = ex_reg_wdata_i;
        end
      end

      dump_printbuffer_to_file();
    end
  end // always_ff @(posedge clk_i)

endmodule
