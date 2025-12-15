/*
 * Copyright 2020 Google LLC
 * Copyright 2023 Frontgrade Gaisler
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

class riscv_zcb_instr extends riscv_instr;

  // This code is based on the frozen v.1.0.1 code reduction specification.
  // Most of the code is copied from the riscv_compressed_instr class.

  constraint rvc_csr_c {
    //  Registers specified by the three-bit rs1’, rs2’, and rd/rs1’
    if (format inside {CLB_FORMAT, CSB_FORMAT, CLH_FORMAT, CSH_FORMAT, CU_FORMAT, CA_FORMAT}) {
      if (has_rs1) {
        rs1 inside {[S0:A5]};
      }
      if (has_rs2) {
        rs2 inside {[S0:A5]};
      }
      if (has_rd) {
        rd inside {[S0:A5]};
      }
    }
    // CU_FORMAT and CA_FORMAT has rd == rs1
    if (format inside {CU_FORMAT, CA_FORMAT}) {
      if (has_rd && has_rs1) {
        rd == rs1;
      }
    }
  }

  `uvm_object_utils(riscv_zcb_instr)

  function new(string name = "");
    super.new(name);
    rs1 = S0;
    rs2 = S0;
    rd  = S0;
    is_compressed = 1'b1;
  endfunction : new

  virtual function void set_imm_len();
    if (format inside {CLB_FORMAT, CSB_FORMAT}) begin
      imm_len = 2;
    end else if (format inside {CLH_FORMAT, CSH_FORMAT}) begin
      imm_len = 1;
    end
  endfunction : set_imm_len

  virtual function void set_rand_mode();
    case (format) inside
      CLB_FORMAT: begin
        has_rs2 = 1'b0;
      end
      CSB_FORMAT: begin
        has_rd = 1'b0;
      end
      CLH_FORMAT: begin
        has_rs2 = 1'b0;
      end
      CSH_FORMAT: begin
        has_rd = 1'b0;
      end
      CU_FORMAT: begin
        has_rs2 = 1'b0;
        has_imm = 1'b0;
      end
      CA_FORMAT: begin
        has_imm = 1'b0;
      end
      default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
    endcase
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    case(format)
      CLB_FORMAT, CLH_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
      CSB_FORMAT, CSH_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
      CU_FORMAT:
        asm_str = $sformatf("%0s%0s", asm_str, rs1.name);
      CA_FORMAT:
        asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
      default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
    endcase

    if (comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction : convert2asm

  // Convert the instruction to assembly code
  virtual function string convert2bin(string prefix = "");
    string binary;
    case (instr_name) inside
      C_LBU:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rs1), imm[0], imm[1],
                                     get_c_gpr(rd), get_c_opcode()});
      C_LHU:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rs1), 1'b0, imm[1],
                                     get_c_gpr(rd), get_c_opcode()});
      C_LH:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rs1), 1'b1, imm[1],
                                     get_c_gpr(rd), get_c_opcode()});
      C_SB:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rs1), imm[0], imm[1],
                                     get_c_gpr(rs2), get_c_opcode()});
      C_SH:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rs1), 1'b0, imm[1],
                                     get_c_gpr(rs2), get_c_opcode()});
      C_ZEXT_B:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rd), 5'b11000,
                                     get_c_opcode()});
      C_SEXT_B:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rd), 5'b11001,
                                     get_c_opcode()});
      C_ZEXT_H:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rd), 5'b11010,
                                     get_c_opcode()});
      C_SEXT_H:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rd), 5'b11011,
                                     get_c_opcode()});
      C_ZEXT_W:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rd), 5'b11100,
                                     get_c_opcode()});
      C_NOT:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rd), 5'b11101,
                                     get_c_opcode()});
      C_MUL:
        binary = $sformatf("0x%4h", {get_func6(), get_c_gpr(rd), 2'b10,
                                     get_c_gpr(rs2), get_c_opcode()});
      default: `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
    return {prefix, binary};
  endfunction : convert2bin

  // Get opcode for zcb instruction
  virtual function bit [1:0] get_c_opcode();
    case (instr_name) inside
      C_ZEXT_B, C_SEXT_B, C_ZEXT_H, C_SEXT_H,
              C_ZEXT_W, C_NOT, C_MUL : get_c_opcode = 2'b01;
      C_LBU, C_LHU, C_LH, C_SB, C_SH : get_c_opcode = 2'b00;
      default: `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction : get_c_opcode

  virtual function bit [5:0] get_func6();
    case (instr_name)
      C_LBU:    get_func6 = 6'b100000;
      C_LHU:    get_func6 = 6'b100001;
      C_LH:     get_func6 = 6'b100001;
      C_SB:     get_func6 = 6'b100010;
      C_SH:     get_func6 = 6'b100011;
      C_ZEXT_B: get_func6 = 6'b100011;
      C_SEXT_B: get_func6 = 6'b100111;
      C_ZEXT_H: get_func6 = 6'b100111;
      C_SEXT_H: get_func6 = 6'b100111;
      C_ZEXT_W: get_func6 = 6'b100111;
      C_NOT:    get_func6 = 6'b100111;
      C_MUL:    get_func6 = 6'b100111;
      default: `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction : get_func6

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    return (cfg.enable_zcb_extension &&
           // RV32C, RV32Zbb, RV32Zba, M/Zmmul is prerequisites for this extension
          (RV32ZBB inside {supported_isa}) &&
          (RV32C inside {supported_isa})   &&
          (RV32ZBA inside {supported_isa}) &&
          ((RV32M inside {supported_isa}) || (RV32ZMMUL inside {supported_isa})) &&
          ((RV32ZCB inside {supported_isa} || RV64ZCB inside {supported_isa}))   &&
           instr_name inside {
              C_ZEXT_B, C_SEXT_B, C_ZEXT_H, C_SEXT_H, C_ZEXT_W,
              C_NOT, C_MUL, C_LBU, C_LHU, C_LH, C_SB, C_SH
           });
  endfunction : is_supported

  // For coverage
  virtual function void update_src_regs(string operands[$]);
    case(format)
      CU_FORMAT: begin
        rs1 = get_gpr(operands[0]);
        rs1_value = get_gpr_state(operands[0]);
      end
      CLB_FORMAT, CLH_FORMAT: begin
        get_val(operands[2], imm);
        rs1 = get_gpr(operands[1]);
        rs1_value = get_gpr_state(operands[1]);
      end
      CSB_FORMAT, CSH_FORMAT: begin
        rs2 = get_gpr(operands[0]);
        rs2_value = get_gpr_state(operands[0]);
        get_val(operands[2], imm);
        rs1 = get_gpr(operands[1]);
        rs1_value = get_gpr_state(operands[1]);
      end
      CA_FORMAT: begin
        rs2 = get_gpr(operands[1]);
        rs2_value = get_gpr_state(operands[1]);
        rs1 = get_gpr(operands[0]);
        rs1_value = get_gpr_state(operands[0]);
      end
      default: ;
    endcase
    super.update_src_regs(operands);
  endfunction : update_src_regs

endclass : riscv_zcb_instr;
