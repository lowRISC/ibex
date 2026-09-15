/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ****************************************************************** */
/* This file specifies the instructions in the base integer set.      */


/* ****************************************************************** */
union clause ast = UTYPE : (bits(20), regidx, uop)

mapping encdec_uop : uop <-> bits(7) = {
  RISCV_LUI   <-> 0b0110111,
  RISCV_AUIPC <-> 0b0010111
}

mapping clause encdec = UTYPE(imm, rd, op)
  <-> imm @ rd @ encdec_uop(op)

function clause execute UTYPE(imm, rd, op) = {
  let off : xlenbits = sign_extend(imm @ 0x000);
  let ret : xlenbits = match op {
    RISCV_LUI   => off,
    RISCV_AUIPC => get_arch_pc() + off
  };
  X(rd) = ret;
  RETIRE_SUCCESS
}

mapping utype_mnemonic : uop <-> string = {
  RISCV_LUI   <-> "lui",
  RISCV_AUIPC <-> "auipc"
}

mapping clause assembly = UTYPE(imm, rd, op)
  <-> utype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_20(imm)

/* ****************************************************************** */
union clause ast = RISCV_JAL : (bits(21), regidx)

mapping clause encdec = RISCV_JAL(imm_19 @ imm_7_0 @ imm_8 @ imm_18_13 @ imm_12_9 @ 0b0, rd)
  <-> imm_19 : bits(1) @ imm_18_13 : bits(6) @ imm_12_9 : bits(4) @ imm_8 : bits(1) @ imm_7_0 : bits(8) @ rd @ 0b1101111

/*
ideally we want some syntax like

mapping clause encdec = RISCV_JAL(imm @ 0b0, rd) <-> imm[19] @ imm[9..0] @ imm[10] @ imm[18..11] @ rd @ 0b1101111

match bv {
  imm[19] @ imm[9..0] @ imm[10] @ imm[18..11] -> imm @ 0b0
}

but this is difficult
*/

function clause execute (RISCV_JAL(imm, rd)) = {
  let t : xlenbits = PC + sign_extend(imm);
  /* Extensions get the first checks on the prospective target address. */
  match ext_control_check_pc(t) {
    Ext_ControlAddr_Error(e) => {
      ext_handle_control_check_error(e);
      RETIRE_FAIL
    },
    Ext_ControlAddr_OK(target) => {
      /* Perform standard alignment check */
      if bit_to_bool(target[1]) & not(haveRVC())
      then {
        handle_mem_exception(target, E_Fetch_Addr_Align());
        RETIRE_FAIL
      } else {
        X(rd) = get_next_pc();
        set_next_pc(target);
        RETIRE_SUCCESS
      }
    }
  }
}

/* TODO: handle 2-byte-alignment in mappings */

mapping clause assembly = RISCV_JAL(imm, rd)
  <-> "jal" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_21(imm)

/* ****************************************************************** */
union clause ast = RISCV_JALR : (bits(12), regidx, regidx)

mapping clause encdec = RISCV_JALR(imm, rs1, rd)
  <-> imm @ rs1 @ 0b000 @ rd @ 0b1100111

mapping clause assembly = RISCV_JALR(imm, rs1, rd)
  <-> "jalr" ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_12(imm) ^ "(" ^ reg_name(rs1) ^ ")"

/* see riscv_jalr_seq.sail or riscv_jalr_rmem.sail for the execute clause. */

/* ****************************************************************** */
union clause ast = BTYPE : (bits(13), regidx, regidx, bop)

mapping encdec_bop : bop <-> bits(3) = {
  RISCV_BEQ  <-> 0b000,
  RISCV_BNE  <-> 0b001,
  RISCV_BLT  <-> 0b100,
  RISCV_BGE  <-> 0b101,
  RISCV_BLTU <-> 0b110,
  RISCV_BGEU <-> 0b111
}

mapping clause encdec = BTYPE(imm7_6 @ imm5_0 @ imm7_5_0 @ imm5_4_1 @ 0b0, rs2, rs1, op)
  <-> imm7_6 : bits(1) @ imm7_5_0 : bits(6) @ rs2 @ rs1 @ encdec_bop(op) @ imm5_4_1 : bits(4) @ imm5_0 : bits(1) @ 0b1100011

function clause execute (BTYPE(imm, rs2, rs1, op)) = {
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  let taken : bool = match op {
    RISCV_BEQ  => rs1_val == rs2_val,
    RISCV_BNE  => rs1_val != rs2_val,
    RISCV_BLT  => rs1_val <_s rs2_val,
    RISCV_BGE  => rs1_val >=_s rs2_val,
    RISCV_BLTU => rs1_val <_u rs2_val,
    RISCV_BGEU => rs1_val >=_u rs2_val
  };
  let t : xlenbits = PC + sign_extend(imm);
  if taken then {
    /* Extensions get the first checks on the prospective target address. */
    match ext_control_check_pc(t) {
      Ext_ControlAddr_Error(e) => {
        ext_handle_control_check_error(e);
        RETIRE_FAIL
      },
      Ext_ControlAddr_OK(target) => {
        if bit_to_bool(target[1]) & not(haveRVC()) then {
          handle_mem_exception(target, E_Fetch_Addr_Align());
          RETIRE_FAIL;
        } else {
          set_next_pc(target);
          RETIRE_SUCCESS
        }
      }
    }
  } else RETIRE_SUCCESS
}

mapping btype_mnemonic : bop <-> string = {
  RISCV_BEQ  <-> "beq",
  RISCV_BNE  <-> "bne",
  RISCV_BLT  <-> "blt",
  RISCV_BGE  <-> "bge",
  RISCV_BLTU <-> "bltu",
  RISCV_BGEU <-> "bgeu"
}

mapping clause assembly = BTYPE(imm, rs2, rs1, op)
  <-> btype_mnemonic(op) ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2) ^ sep() ^ hex_bits_13(imm)

/* ****************************************************************** */
union clause ast = ITYPE : (bits(12), regidx, regidx, iop)

mapping encdec_iop : iop <-> bits(3) = {
  RISCV_ADDI  <-> 0b000,
  RISCV_SLTI  <-> 0b010,
  RISCV_SLTIU <-> 0b011,
  RISCV_ANDI  <-> 0b111,
  RISCV_ORI   <-> 0b110,
  RISCV_XORI  <-> 0b100
}

mapping clause encdec = ITYPE(imm, rs1, rd, op)
  <-> imm @ rs1 @ encdec_iop(op) @ rd @ 0b0010011

function clause execute (ITYPE (imm, rs1, rd, op)) = {
  let rs1_val = X(rs1, rs_1);
  let immext : xlenbits = sign_extend(imm);
  let result : xlenbits = match op {
    RISCV_ADDI  => rs1_val + immext,
    RISCV_SLTI  => zero_extend(bool_to_bits(rs1_val <_s immext)),
    RISCV_SLTIU => zero_extend(bool_to_bits(rs1_val <_u immext)),
    RISCV_ANDI  => rs1_val & immext,
    RISCV_ORI   => rs1_val | immext,
    RISCV_XORI  => rs1_val ^ immext
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping itype_mnemonic : iop <-> string = {
  RISCV_ADDI  <-> "addi",
  RISCV_SLTI  <-> "slti",
  RISCV_SLTIU <-> "sltiu",
  RISCV_XORI  <-> "xori",
  RISCV_ORI   <-> "ori",
  RISCV_ANDI  <-> "andi"
}

mapping clause assembly = ITYPE(imm, rs1, rd, op)
  <-> itype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)

/* ****************************************************************** */
union clause ast = SHIFTIOP : (bits(6), regidx, regidx, sop)

mapping encdec_sop : sop <-> bits(3) = {
  RISCV_SLLI <-> 0b001,
  RISCV_SRLI <-> 0b101,
  RISCV_SRAI <-> 0b101
}

mapping clause encdec = SHIFTIOP(shamt, rs1, rd, RISCV_SLLI) <-> 0b000000 @ shamt @ rs1 @ 0b001 @ rd @ 0b0010011 if sizeof(xlen) == 64 | shamt[5] == bitzero
mapping clause encdec = SHIFTIOP(shamt, rs1, rd, RISCV_SRLI) <-> 0b000000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 64 | shamt[5] == bitzero
mapping clause encdec = SHIFTIOP(shamt, rs1, rd, RISCV_SRAI) <-> 0b010000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0010011 if sizeof(xlen) == 64 | shamt[5] == bitzero

function clause execute (SHIFTIOP(shamt, rs1, rd, op)) = {
  let rs1_val = X(rs1, rs_1);
  /* the decoder guard should ensure that shamt[5] = 0 for RV32 */
  let result : xlenbits = match op {
    RISCV_SLLI => if   sizeof(xlen) == 32
                  then rs1_val << shamt[4..0]
                  else rs1_val << shamt,
    RISCV_SRLI => if   sizeof(xlen) == 32
                  then rs1_val >> shamt[4..0]
                  else rs1_val >> shamt,
    RISCV_SRAI => if   sizeof(xlen) == 32
                  then shift_right_arith32(rs1_val, shamt[4..0])
                  else shift_right_arith64(rs1_val, shamt)
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping shiftiop_mnemonic : sop <-> string = {
  RISCV_SLLI <-> "slli",
  RISCV_SRLI <-> "srli",
  RISCV_SRAI <-> "srai"
}

mapping clause assembly = SHIFTIOP(shamt, rs1, rd, op)
  <-> shiftiop_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_6(shamt)

/* ****************************************************************** */
union clause ast = RTYPE : (regidx, regidx, regidx, rop)

mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_ADD)  <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SLT)  <-> 0b0000000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SLTU) <-> 0b0000000 @ rs2 @ rs1 @ 0b011 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_AND)  <-> 0b0000000 @ rs2 @ rs1 @ 0b111 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_OR)   <-> 0b0000000 @ rs2 @ rs1 @ 0b110 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_XOR)  <-> 0b0000000 @ rs2 @ rs1 @ 0b100 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SLL)  <-> 0b0000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SRL)  <-> 0b0000000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SUB)  <-> 0b0100000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0110011
mapping clause encdec = RTYPE(rs2, rs1, rd, RISCV_SRA)  <-> 0b0100000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0110011

function clause execute (RTYPE(rs2, rs1, rd, op)) = {
  let rs1_val = X(rs1, rs_1);
  let rs2_val = X(rs2, rs_2);
  let result : xlenbits = match op {
    RISCV_ADD  => rs1_val + rs2_val,
    RISCV_SLT  => zero_extend(bool_to_bits(rs1_val <_s rs2_val)),
    RISCV_SLTU => zero_extend(bool_to_bits(rs1_val <_u rs2_val)),
    RISCV_AND  => rs1_val & rs2_val,
    RISCV_OR   => rs1_val | rs2_val,
    RISCV_XOR  => rs1_val ^ rs2_val,
    RISCV_SLL  => if   sizeof(xlen) == 32
                  then rs1_val << (rs2_val[4..0])
                  else rs1_val << (rs2_val[5..0]),
    RISCV_SRL  => if   sizeof(xlen) == 32
                  then rs1_val >> (rs2_val[4..0])
                  else rs1_val >> (rs2_val[5..0]),
    RISCV_SUB  => rs1_val - rs2_val,
    RISCV_SRA  => if   sizeof(xlen) == 32
                  then shift_right_arith32(rs1_val, rs2_val[4..0])
                  else shift_right_arith64(rs1_val, rs2_val[5..0])
  };
  X(rd) = result;
  RETIRE_SUCCESS
}

mapping rtype_mnemonic : rop <-> string = {
  RISCV_ADD  <-> "add",
  RISCV_SLT  <-> "slt",
  RISCV_SLTU <-> "sltu",
  RISCV_AND  <-> "and",
  RISCV_OR   <-> "or",
  RISCV_XOR  <-> "xor",
  RISCV_SLL  <-> "sll",
  RISCV_SRL  <-> "srl",
  RISCV_SUB  <-> "sub",
  RISCV_SRA  <-> "sra"
}

mapping clause assembly = RTYPE(rs2, rs1, rd, op)
  <-> rtype_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)

/* ****************************************************************** */
union clause ast = LOAD : (bits(12), regidx, regidx, bool, word_width, bool, bool)

/* unsigned loads are only present for widths strictly less than xlen,
   signed loads also present for widths equal to xlen */
mapping clause encdec = LOAD(imm, rs1, rd, is_unsigned, size, false, false) if (word_width_bytes(size) < sizeof(xlen_bytes)) | (not(is_unsigned) & word_width_bytes(size) <= sizeof(xlen_bytes))
  <-> imm @ rs1 @ bool_bits(is_unsigned) @ size_bits(size) @ rd @ 0b0000011 if (word_width_bytes(size) < sizeof(xlen_bytes)) | (not(is_unsigned) & word_width_bytes(size) <= sizeof(xlen_bytes))

val extend_value : forall 'n, 0 < 'n <= xlen_bytes. (bool, MemoryOpResult(bits(8 * 'n))) -> MemoryOpResult(xlenbits)
function extend_value(is_unsigned, value) = match (value) {
  MemValue(v)     => MemValue(if is_unsigned then zero_extend(v) else sign_extend(v) : xlenbits),
  MemException(e) => MemException(e)
}

val process_load : forall 'n, 0 < 'n <= xlen_bytes. (regidx, xlenbits, MemoryOpResult(bits(8 * 'n)), bool) -> Retired
function process_load(rd, vaddr, value, is_unsigned) =
  match extend_value(is_unsigned, value) {
    MemValue(result) => { X(rd) = result; RETIRE_SUCCESS },
    MemException(e)  => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
  }

function check_misaligned(vaddr : xlenbits, width : word_width) -> bool =
  if   plat_enable_misaligned_access() then false
  else match width {
         BYTE   => false,
         HALF   => vaddr[0] == bitone,
         WORD   => vaddr[0] == bitone | vaddr[1] == bitone,
         DOUBLE => vaddr[0] == bitone | vaddr[1] == bitone | vaddr[2] == bitone
       }

function clause execute(LOAD(imm, rs1, rd, is_unsigned, width, aq, rl)) = {
  let offset : xlenbits = sign_extend(imm);
  /* Get the address, X(rs1) + offset.
     Some extensions perform additional checks on address validity. */
  match ext_data_get_addr(rs1, offset, Read(Data), width) {
    Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); RETIRE_FAIL },
    Ext_DataAddr_OK(vaddr) =>
      if   check_misaligned(vaddr, width)
      then { handle_mem_exception(vaddr, E_Load_Addr_Align()); RETIRE_FAIL }
      else match translateAddr(vaddr, Read(Data)) {
        TR_Failure(e, _) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(paddr, _) =>
          match (width) {
            BYTE =>
              process_load(rd, vaddr, mem_read(Read(Data), paddr, 1, aq, rl, false), is_unsigned),
            HALF =>
              process_load(rd, vaddr, mem_read(Read(Data), paddr, 2, aq, rl, false), is_unsigned),
            WORD =>
              process_load(rd, vaddr, mem_read(Read(Data), paddr, 4, aq, rl, false), is_unsigned),
            DOUBLE if sizeof(xlen) >= 64 =>
              process_load(rd, vaddr, mem_read(Read(Data), paddr, 8, aq, rl, false), is_unsigned),
            _ => report_invalid_width(__FILE__, __LINE__, width, "load")
          }
      }
  }
}

val maybe_aq : bool <-> string
mapping maybe_aq = {
  true  <-> ".aq",
  false <-> ""
}

val maybe_rl : bool <-> string
mapping maybe_rl = {
  true  <-> ".rl",
  false <-> ""
}

val maybe_u : bool <-> string
mapping maybe_u = {
  true  <-> "u",
  false <-> ""
}

mapping clause assembly = LOAD(imm, rs1, rd, is_unsigned, size, aq, rl)
  <-> "l" ^ size_mnemonic(size) ^ maybe_u(is_unsigned) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ hex_bits_12(imm) ^ "(" ^ reg_name(rs1) ^ ")"

/* ****************************************************************** */
union clause ast = STORE : (bits(12), regidx, regidx, word_width, bool, bool)

mapping clause encdec = STORE(imm7 @ imm5, rs2, rs1, size, false, false)              if word_width_bytes(size) <= sizeof(xlen_bytes)
  <-> imm7 : bits(7) @ rs2 @ rs1 @ 0b0 @ size_bits(size) @ imm5 : bits(5) @ 0b0100011 if word_width_bytes(size) <= sizeof(xlen_bytes)

/* NOTE: Currently, we only EA if address translation is successful.
   This may need revisiting. */
function clause execute (STORE(imm, rs2, rs1, width, aq, rl)) = {
  let offset : xlenbits = sign_extend(imm);
  /* Get the address, X(rs1) + offset.
     Some extensions perform additional checks on address validity. */
  match ext_data_get_addr(rs1, offset, Write(Data), width) {
    Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); RETIRE_FAIL },
    Ext_DataAddr_OK(vaddr) =>
      if   check_misaligned(vaddr, width)
      then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); RETIRE_FAIL }
      else match translateAddr(vaddr, Write(Data)) {
        TR_Failure(e, _)    => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(paddr, _) => {
          let eares : MemoryOpResult(unit) = match width {
            BYTE   => mem_write_ea(paddr, 1, aq, rl, false),
            HALF   => mem_write_ea(paddr, 2, aq, rl, false),
            WORD   => mem_write_ea(paddr, 4, aq, rl, false),
            DOUBLE => mem_write_ea(paddr, 8, aq, rl, false)
          };
          match (eares) {
            MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
            MemValue(_) => {
              let rs2_val = X(rs2, rs_2);
              let res : MemoryOpResult(bool) = match (width) {
                BYTE => mem_write_value(paddr, 1, rs2_val[7..0],  aq, rl, false),
                HALF => mem_write_value(paddr, 2, rs2_val[15..0], aq, rl, false),
                WORD => mem_write_value(paddr, 4, rs2_val[31..0], aq, rl, false),
                DOUBLE if sizeof(xlen) >= 64
                     => mem_write_value(paddr, 8, rs2_val,        aq, rl, false),
                _    => report_invalid_width(__FILE__, __LINE__, width, "store"),
              };
              match (res) {
                MemValue(true)  => RETIRE_SUCCESS,
                MemValue(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
                MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
              }
            }
          }
        }
      }
  }
}

mapping clause assembly = STORE(imm, rs2, rs1, size, aq, rl)
  <-> "s" ^ size_mnemonic(size) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rs2) ^ sep() ^ hex_bits_12(imm) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"

/* ****************************************************************** */
union clause ast = ADDIW : (bits(12), regidx, regidx)

mapping clause encdec = ADDIW(imm, rs1, rd)
      if sizeof(xlen) == 64
  <-> imm @ rs1 @ 0b000 @ rd @ 0b0011011
      if sizeof(xlen) == 64

function clause execute (ADDIW(imm, rs1, rd)) = {
  let result : xlenbits = sign_extend(imm) + X(rs1, rs_1);
  X(rd) = sign_extend(result[31..0]);
  RETIRE_SUCCESS
}

mapping clause assembly = ADDIW(imm, rs1, rd)
      if sizeof(xlen) == 64
  <-> "addiw" ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_12(imm)
      if sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = RTYPEW : (regidx, regidx, regidx, ropw)

mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_ADDW)
      if sizeof(xlen) == 64
  <-> 0b0000000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
      if sizeof(xlen) == 64
mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_SUBW)
      if sizeof(xlen) == 64
  <-> 0b0100000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b0111011
      if sizeof(xlen) == 64
mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_SLLW)
      if sizeof(xlen) == 64
  <-> 0b0000000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b0111011
      if sizeof(xlen) == 64
mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_SRLW)
      if sizeof(xlen) == 64
  <-> 0b0000000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
      if sizeof(xlen) == 64
mapping clause encdec = RTYPEW(rs2, rs1, rd, RISCV_SRAW)
      if sizeof(xlen) == 64
  <-> 0b0100000 @ rs2 @ rs1 @ 0b101 @ rd @ 0b0111011
      if sizeof(xlen) == 64

function clause execute (RTYPEW(rs2, rs1, rd, op)) = {
  let rs1_val = (X(rs1, rs_1))[31..0];
  let rs2_val = (X(rs2, rs_2))[31..0];
  let result : bits(32) = match op {
    RISCV_ADDW => rs1_val + rs2_val,
    RISCV_SUBW => rs1_val - rs2_val,
    RISCV_SLLW => rs1_val << (rs2_val[4..0]),
    RISCV_SRLW => rs1_val >> (rs2_val[4..0]),
    RISCV_SRAW => shift_right_arith32(rs1_val, rs2_val[4..0])
  };
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

mapping rtypew_mnemonic : ropw <-> string = {
  RISCV_ADDW <-> "addw",
  RISCV_SUBW <-> "subw",
  RISCV_SLLW <-> "sllw",
  RISCV_SRLW <-> "srlw",
  RISCV_SRAW <-> "sraw"
}

mapping clause assembly = RTYPEW(rs2, rs1, rd, op)
      if sizeof(xlen) == 64
  <-> rtypew_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
      if sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = SHIFTIWOP : (bits(5), regidx, regidx, sopw)

mapping clause encdec = SHIFTIWOP(shamt, rs1, rd, RISCV_SLLIW)
      if sizeof(xlen) == 64
  <-> 0b0000000 @ shamt @ rs1 @ 0b001 @ rd @ 0b0011011
      if sizeof(xlen) == 64
mapping clause encdec = SHIFTIWOP(shamt, rs1, rd, RISCV_SRLIW)
      if sizeof(xlen) == 64
  <-> 0b0000000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0011011
      if sizeof(xlen) == 64
mapping clause encdec = SHIFTIWOP(shamt, rs1, rd, RISCV_SRAIW)
      if sizeof(xlen) == 64
  <-> 0b0100000 @ shamt @ rs1 @ 0b101 @ rd @ 0b0011011
      if sizeof(xlen) == 64

function clause execute (SHIFTIWOP(shamt, rs1, rd, op)) = {
  let rs1_val = (X(rs1, rs_1))[31..0];
  let result : bits(32) = match op {
    RISCV_SLLIW => rs1_val << shamt,
    RISCV_SRLIW => rs1_val >> shamt,
    RISCV_SRAIW => shift_right_arith32(rs1_val, shamt)
  };
  X(rd) = sign_extend(result);
  RETIRE_SUCCESS
}

mapping shiftiwop_mnemonic : sopw <-> string = {
  RISCV_SLLIW <-> "slliw",
  RISCV_SRLIW <-> "srliw",
  RISCV_SRAIW <-> "sraiw"
}

mapping clause assembly = SHIFTIWOP(shamt, rs1, rd, op)
      if sizeof(xlen) == 64
  <-> shiftiwop_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs1) ^ sep() ^ hex_bits_5(shamt)
      if sizeof(xlen) == 64

/* ****************************************************************** */
union clause ast = FENCE : (bits(4), bits(4))

mapping clause encdec = FENCE(pred, succ)
  <-> 0b0000 @ pred @ succ @ 0b00000 @ 0b000 @ 0b00000 @ 0b0001111

function effective_fence_set(set : bits(4), fiom : bool) -> bits(4) = {
  // The bits are IORW. If FIOM is set then I implies R and O implies W.
  if fiom then {
    set[3 .. 2] @ (set[1 .. 0] | set[3 .. 2])
  } else set
}

/* For future versions of Sail where barriers can be parameterised */
$ifdef FEATURE_UNION_BARRIER

function clause execute (FENCE(pred, succ)) = {
  // If the FIOM bit in menvcfg/senvcfg is set then the I/O bits can imply R/W.
  let fiom = is_fiom_active();
  let pred = effective_fence_set(pred, fiom);
  let succ = effective_fence_set(succ, fiom);

  match (pred, succ) {
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b11) => __barrier(Barrier_RISCV_rw_rw()),
    (_ : bits(2) @ 0b10, _ : bits(2) @ 0b11) => __barrier(Barrier_RISCV_r_rw()),
    (_ : bits(2) @ 0b10, _ : bits(2) @ 0b10) => __barrier(Barrier_RISCV_r_r()),
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b01) => __barrier(Barrier_RISCV_rw_w()),
    (_ : bits(2) @ 0b01, _ : bits(2) @ 0b01) => __barrier(Barrier_RISCV_w_w()),
    (_ : bits(2) @ 0b01, _ : bits(2) @ 0b11) => __barrier(Barrier_RISCV_w_rw()),
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b10) => __barrier(Barrier_RISCV_rw_r()),
    (_ : bits(2) @ 0b10, _ : bits(2) @ 0b01) => __barrier(Barrier_RISCV_r_w()),
    (_ : bits(2) @ 0b01, _ : bits(2) @ 0b10) => __barrier(Barrier_RISCV_w_r()),

    (_ : bits(4)       , _ : bits(2) @ 0b00) => (),
    (_ : bits(2) @ 0b00, _ : bits(4)       ) => (),

    _ => { print("FIXME: unsupported fence");
           () }
  };
  RETIRE_SUCCESS
}

$else

function clause execute (FENCE(pred, succ)) = {
  // If the FIOM bit in menvcfg/senvcfg is set then the I/O bits can imply R/W.
  let fiom = is_fiom_active();
  let pred = effective_fence_set(pred, fiom);
  let succ = effective_fence_set(succ, fiom);

  match (pred, succ) {
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b11) => __barrier(Barrier_RISCV_rw_rw),
    (_ : bits(2) @ 0b10, _ : bits(2) @ 0b11) => __barrier(Barrier_RISCV_r_rw),
    (_ : bits(2) @ 0b10, _ : bits(2) @ 0b10) => __barrier(Barrier_RISCV_r_r),
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b01) => __barrier(Barrier_RISCV_rw_w),
    (_ : bits(2) @ 0b01, _ : bits(2) @ 0b01) => __barrier(Barrier_RISCV_w_w),
    (_ : bits(2) @ 0b01, _ : bits(2) @ 0b11) => __barrier(Barrier_RISCV_w_rw),
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b10) => __barrier(Barrier_RISCV_rw_r),
    (_ : bits(2) @ 0b10, _ : bits(2) @ 0b01) => __barrier(Barrier_RISCV_r_w),
    (_ : bits(2) @ 0b01, _ : bits(2) @ 0b10) => __barrier(Barrier_RISCV_w_r),

    (_ : bits(4)       , _ : bits(2) @ 0b00) => (),
    (_ : bits(2) @ 0b00, _ : bits(4)       ) => (),

    _ => { print("FIXME: unsupported fence");
           () }
  };
  RETIRE_SUCCESS
}

$endif

mapping bit_maybe_r : bits(1) <-> string = {
  0b1 <-> "r",
  0b0 <-> ""
}

mapping bit_maybe_w : bits(1) <-> string = {
  0b1 <-> "w",
  0b0 <-> ""
}

mapping bit_maybe_i : bits(1) <-> string = {
  0b1 <-> "i",
  0b0 <-> ""
}

mapping bit_maybe_o : bits(1) <-> string = {
  0b1 <-> "o",
  0b0 <-> ""
}

mapping fence_bits : bits(4) <-> string = {
  i : bits(1) @ o : bits(1) @ r : bits(1) @ w : bits(1) <-> bit_maybe_i(i) ^ bit_maybe_o(o) ^ bit_maybe_r(r) ^ bit_maybe_w(w)
}

mapping clause assembly = FENCE(pred, succ)
  <-> "fence" ^ spc() ^ fence_bits(pred) ^ sep() ^ fence_bits(succ)

/* ****************************************************************** */
union clause ast = FENCE_TSO : (bits(4), bits(4))

mapping clause encdec = FENCE_TSO(pred, succ)
  <-> 0b1000 @ pred @ succ @ 0b00000 @ 0b000 @ 0b00000 @ 0b0001111

$ifdef FEATURE_UNION_BARRIER

function clause execute (FENCE_TSO(pred, succ)) = {
  match (pred, succ) {
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b11) => __barrier(Barrier_RISCV_tso()),
    (_ : bits(2) @ 0b00, _ : bits(2) @ 0b00) => (),

    _ => { print("FIXME: unsupported fence");
           () }
  };
  RETIRE_SUCCESS
}

$else

function clause execute (FENCE_TSO(pred, succ)) = {
  match (pred, succ) {
    (_ : bits(2) @ 0b11, _ : bits(2) @ 0b11) => __barrier(Barrier_RISCV_tso),
    (_ : bits(2) @ 0b00, _ : bits(2) @ 0b00) => (),

    _ => { print("FIXME: unsupported fence");
           () }
  };
  RETIRE_SUCCESS
}

$endif

mapping clause assembly = FENCE_TSO(pred, succ)
  <-> "fence.tso" ^ spc() ^ fence_bits(pred) ^ sep() ^ fence_bits(succ)

/* ****************************************************************** */
union clause ast = FENCEI : unit

mapping clause encdec = FENCEI()
  <-> 0b000000000000 @ 0b00000 @ 0b001 @ 0b00000 @ 0b0001111

/* fence.i is a nop for the memory model */
function clause execute FENCEI() = { /* __barrier(Barrier_RISCV_i); */ RETIRE_SUCCESS }

mapping clause assembly = FENCEI() <-> "fence.i"

/* ****************************************************************** */
union clause ast = ECALL : unit

mapping clause encdec = ECALL()
  <-> 0b000000000000 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute ECALL() = {
  let t : sync_exception =
    struct { trap = match (cur_privilege) {
                      User       => E_U_EnvCall(),
                      Supervisor => E_S_EnvCall(),
                      Machine    => E_M_EnvCall()
                    },
             excinfo = (None() : option(xlenbits)),
             ext     = None() };
  set_next_pc(exception_handler(cur_privilege, CTL_TRAP(t), PC));
  RETIRE_FAIL
}

mapping clause assembly = ECALL() <-> "ecall"

/* ****************************************************************** */
union clause ast = MRET : unit

mapping clause encdec = MRET()
  <-> 0b0011000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute MRET() = {
  if   cur_privilege != Machine
  then { handle_illegal(); RETIRE_FAIL }
  else if not(ext_check_xret_priv (Machine))
  then { ext_fail_xret_priv(); RETIRE_FAIL }
  else {
    set_next_pc(exception_handler(cur_privilege, CTL_MRET(), PC));
    RETIRE_SUCCESS
  }
}

mapping clause assembly = MRET() <-> "mret"

/* ****************************************************************** */
union clause ast = SRET : unit

mapping clause encdec = SRET()
  <-> 0b0001000 @ 0b00010 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute SRET() = {
  let sret_illegal : bool = match cur_privilege {
    User       => true,
    Supervisor => not(haveSupMode ()) | mstatus[TSR] == 0b1,
    Machine    => not(haveSupMode ())
  };
  if   sret_illegal
  then { handle_illegal(); RETIRE_FAIL }
  else if not(ext_check_xret_priv (Supervisor))
  then { ext_fail_xret_priv(); RETIRE_FAIL }
  else {
    set_next_pc(exception_handler(cur_privilege, CTL_SRET(), PC));
    RETIRE_SUCCESS
  }
}

mapping clause assembly = SRET() <-> "sret"

/* ****************************************************************** */
union clause ast = EBREAK : unit

mapping clause encdec = EBREAK()
  <-> 0b000000000001 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute EBREAK() = {
  handle_mem_exception(PC, E_Breakpoint());
  RETIRE_FAIL
}

mapping clause assembly = EBREAK() <-> "ebreak"

/* ****************************************************************** */
union clause ast = WFI : unit

mapping clause encdec = WFI()
  <-> 0b000100000101 @ 0b00000 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute WFI() =
  match cur_privilege {
    Machine    => { platform_wfi(); RETIRE_SUCCESS },
    Supervisor => if   mstatus[TW] == 0b1
                  then { handle_illegal(); RETIRE_FAIL }
                  else { platform_wfi(); RETIRE_SUCCESS },
    User       => { handle_illegal(); RETIRE_FAIL }
  }

mapping clause assembly = WFI() <-> "wfi"

/* ****************************************************************** */
union clause ast = SFENCE_VMA : (regidx, regidx)

mapping clause encdec = SFENCE_VMA(rs1, rs2)
  <-> 0b0001001 @ rs2 @ rs1 @ 0b000 @ 0b00000 @ 0b1110011

function clause execute SFENCE_VMA(rs1, rs2) = {
  let addr : option(xlenbits) = if rs1 == 0b00000 then None() else Some(X(rs1, rs_1));
  let asid : option(xlenbits) = if rs2 == 0b00000 then None() else Some(X(rs2, rs_2));
  match cur_privilege {
    User       => { handle_illegal(); RETIRE_FAIL },
    Supervisor => match (architecture(get_mstatus_SXL(mstatus)), mstatus[TVM]) {
                    (Some(_), 0b1)  => { handle_illegal(); RETIRE_FAIL },
                    (Some(_), 0b0) => { flush_TLB(asid, addr); RETIRE_SUCCESS },
                    (_, _)           => internal_error(__FILE__, __LINE__, "unimplemented sfence architecture")
                  },
    Machine    => { flush_TLB(asid, addr); RETIRE_SUCCESS }
  }
}

mapping clause assembly = SFENCE_VMA(rs1, rs2)
  <-> "sfence.vma" ^ spc() ^ reg_name(rs1) ^ sep() ^ reg_name(rs2)
