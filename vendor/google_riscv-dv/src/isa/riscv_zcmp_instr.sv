/*
 * Copyright 2025 Google LLC
 * Copyright 2025 lowRISC CIC
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

class riscv_zcmp_instr extends riscv_instr;

  constraint rvc_csr_c {
    // Solve the stack adjustment first, so we can control the stack size
    solve stack_adj before rlist;
    if (format == CMPP_FORMAT) {
      if (instr_name == CM_PUSH) {
        // For PUSH, stack adjustment is negative
        stack_adj inside {-16, -32, -48, -64, -80, -96, -112};
        (stack_adj == -16)  -> rlist inside {[4:7]};
        (stack_adj == -32)  -> rlist inside {[4:11]};
        (stack_adj == -48)  -> rlist inside {[4:14]};
        (stack_adj == -64)  -> rlist inside {[4:15]};
        (stack_adj == -80)  -> rlist inside {[8:15]};
        (stack_adj == -96)  -> rlist inside {[12:15]};
        (stack_adj == -112) -> rlist inside {15};
      } else {
        // For POP and POPRET, stack adjustment is positive
        stack_adj inside {16, 32, 48, 64, 80, 96, 112};
        (rlist inside {[4:7]})   -> stack_adj inside {16, 32, 48, 64};
        (rlist inside {[8:11]})  -> stack_adj inside {32, 48, 64, 80};
        (rlist inside {[12:14]}) -> stack_adj inside {48, 64, 80, 96};
        (rlist == 15)            -> stack_adj inside {64, 80, 96, 112};
      }
      // rlist can be anything between 4 and 15. 0-3 are reserved for future use.
      rlist inside {[4:15]};
    }
    if (format == CMMV_FORMAT) {
      // Always has rs1 and rs2 and they must be different
      rs1 != rs2;
      // Those instructions use a special encoding, only S0, S1, S2-S7 are allowed
      // which correspond to x8, x9, x18-x23, so the actual registers used are
      // {r1sc[2:1]>0,r1sc[2:1]==0,r1sc[2:0]};
      // So for registers beyond x16 we prepend 0x10 to the three LSB
      // For the registers x8 and x9 we prepend 0x01 to the three LSB
      rs1 inside {S0, S1, [S2:S7]};
      rs2 inside {S0, S1, [S2:S7]};
    }
  }

  `uvm_object_utils(riscv_zcmp_instr)

  function new(string name = "");
    super.new(name);
    rs1 = S0;
    rs2 = S0;
    rlist = 4;
    is_compressed = 1'b1;
    stack_adj = instr_name == CM_PUSH ? -16 : 16;
  endfunction : new

  virtual function void set_rand_mode();
    case (format) inside
      CMMV_FORMAT : begin
        has_imm = 1'b0;
      end
      CMPP_FORMAT : begin
        has_rs1 = 1'b0;
        has_rs2 = 1'b0;
        has_rd = 1'b0;
        has_rlist = 1'b1;
        has_imm = 1'b0;
        has_stack_adj = 1'b1;
      end
      default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
    endcase
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    case(format)
      CMMV_FORMAT:
        asm_str = $sformatf("%0s %0s, %0s", asm_str, rs1.name(), rs2.name());
      CMPP_FORMAT: begin
        asm_str = $sformatf("%0s %0s, %0d", asm_str, get_rlist(), get_stack_adj());
      end
      default: `uvm_info(`gfn, $sformatf("Unsupported format %0s", format.name()), UVM_LOW)
    endcase

    if (comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction : convert2asm

  // Convert the instruction to binary code
  virtual function string convert2bin(string prefix = "");
    string binary;
    case (instr_name) inside
      CM_PUSH:
      binary = $sformatf(
          "0x%4h", {get_func6(), get_func2(), rlist, get_stack_adj_encoding(), get_c_opcode()});
      CM_POP:
      binary = $sformatf(
          "0x%4h", {get_func6(), get_func2(), rlist, get_stack_adj_encoding(), get_c_opcode()});
      CM_POPRETZ:
      binary = $sformatf(
          "0x%4h", {get_func6(), get_func2(), rlist, get_stack_adj_encoding(), get_c_opcode()});
      CM_POPRET:
      binary = $sformatf(
          "0x%4h", {get_func6(), get_func2(), rlist, get_stack_adj_encoding(), get_c_opcode()});
      CM_MVA01S:
      binary = $sformatf(
          "0x%4h", {get_func6(), get_c_gpr(rs1), get_func2(), get_c_gpr(rs2), get_c_opcode()});
      CM_MVSA01:
      binary = $sformatf(
          "0x%4h", {get_func6(), get_c_gpr(rs1), get_func2(), get_c_gpr(rs2), get_c_opcode()});
      default: `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
    return {prefix, binary};
  endfunction : convert2bin

  // Get opcode for zcmp instruction
  virtual function bit [1:0] get_c_opcode();
    case (instr_name) inside
      CM_PUSH, CM_POP, CM_POPRETZ, CM_POPRET, CM_MVA01S, CM_MVSA01 : get_c_opcode = 2'b10;
      default: `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction : get_c_opcode

  virtual function bit [5:0] get_func6();
    case (instr_name) inside
      CM_PUSH:    get_func6 = 6'b101110;
      CM_POP:     get_func6 = 6'b101110;
      CM_POPRETZ: get_func6 = 6'b101111;
      CM_POPRET:  get_func6 = 6'b101111;
      CM_MVSA01:  get_func6 = 6'b101011;
      CM_MVA01S:  get_func6 = 6'b101011;
      default: `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction : get_func6

  virtual function bit [1:0] get_func2();
    case (instr_name) inside
      CM_PUSH:    get_func2 = 2'b00;
      CM_POP:     get_func2 = 2'b10;
      CM_POPRETZ: get_func2 = 2'b00;
      CM_POPRET:  get_func2 = 2'b10;
      CM_MVSA01:  get_func2 = 2'b01;
      CM_MVA01S:  get_func2 = 2'b11;
      default: `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction : get_func2

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    `uvm_info(`gfn, "ZCMP Check supported", UVM_LOW)
    return (cfg.enable_zcmp_extension &&
           // RV32C, RV32Zbb, RV32Zba, M/Zmmul is prerequisites for this extension
          (RV32C inside {supported_isa} || RV64C inside {supported_isa}) &&
          (RV32ZCMP inside {supported_isa} || RV64ZCMP inside {supported_isa})   &&
           instr_name inside {
              CM_PUSH, CM_POP, CM_POPRET, CM_POPRETZ, CM_MVA01S, CM_MVSA01
           });
  endfunction : is_supported

  // For coverage
  virtual function void update_src_regs(string operands[$]);
    case(format)
      CMMV_FORMAT: begin
        rs1 = get_gpr(operands[0]);
        rs1_value = get_gpr_state(operands[0]);
        rs2 = get_gpr(operands[1]);
        rs2_value = get_gpr_state(operands[1]);
      end
      CMPP_FORMAT: begin
        get_val(operands[0], rlist);
        get_val(operands[1], stack_adj);
      end
      default: ;
    endcase
    super.update_src_regs(operands);
  endfunction : update_src_regs

  virtual function bit [1:0] get_stack_adj_encoding();
    int unsigned stack_adj_base;
    int unsigned stack_adj_abs;
    bit [1:0] stack_adj_encoding;
    if (XLEN == 32) begin
      case (rlist)
        4, 5, 6, 7:   stack_adj_base = 16;
        8, 9, 10, 11: stack_adj_base = 32;
        12, 13, 14:   stack_adj_base = 48;
        15:           stack_adj_base = 64;
        default:      stack_adj_base = 0;
      endcase
    end else begin
      case (rlist)
        4, 5:    stack_adj_base = 16;
        6, 7:    stack_adj_base = 32;
        8, 9:    stack_adj_base = 48;
        10, 11:  stack_adj_base = 64;
        12, 13:  stack_adj_base = 80;
        14:      stack_adj_base = 96;
        15:      stack_adj_base = 122;
        default: stack_adj_base = 0;
      endcase
    end
    stack_adj_abs = instr_name == CM_PUSH ? -stack_adj : stack_adj;
    stack_adj_encoding = (stack_adj_abs - stack_adj_base) / 16;
    return stack_adj_encoding;
  endfunction

  virtual function int get_stack_adj();
    return stack_adj;
  endfunction

endclass : riscv_zcmp_instr;
