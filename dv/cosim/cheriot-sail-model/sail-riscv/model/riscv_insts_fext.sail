/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* **************************************************************** */
/* This file specifies the instructions in the F extension          */
/* (single precision floating point).                               */

/* RISC-V follows IEEE 754-2008 floating point arithmetic standard. */

/* Original version written by Rishiyur S. Nikhil, Sept-Oct 2019    */

/* **************************************************************** */
/* IMPORTANT!                                                       */
/* The files 'riscv_insts_fext.sail', 'riscv_insts_dext.sail' and   */
/* 'riscv_insts_zfh.sail' define the F, D and Zfh extensions,       */
/* respectively.                                                    */
/* The texts follow each other very closely; please try to maintain */
/* this correspondence as the files are maintained for bug-fixes,   */
/* improvements, and version updates.                               */

/* **************************************************************** */

mapping encdec_rounding_mode : rounding_mode <-> bits(3) = {
  RM_RNE <-> 0b000,
  RM_RTZ <-> 0b001,
  RM_RDN <-> 0b010,
  RM_RUP <-> 0b011,
  RM_RMM <-> 0b100,
  RM_DYN <-> 0b111
}

mapping frm_mnemonic : rounding_mode <-> string = {
  RM_RNE <-> "rne",
  RM_RTZ <-> "rtz",
  RM_RDN <-> "rdn",
  RM_RUP <-> "rup",
  RM_RMM <-> "rmm",
  RM_DYN <-> "dyn"
}

val      valid_rounding_mode : bits(3) -> bool
function valid_rounding_mode rm = (rm != 0b101 & rm != 0b110)

val      select_instr_or_fcsr_rm : rounding_mode -> option(rounding_mode)
function select_instr_or_fcsr_rm instr_rm =
  if (instr_rm == RM_DYN)
  then {
    let fcsr_rm = fcsr[FRM];
    if (valid_rounding_mode(fcsr_rm) & fcsr_rm != encdec_rounding_mode(RM_DYN))
      then Some(encdec_rounding_mode(fcsr_rm)) else None()
  }
  else Some(instr_rm)

/* **************************************************************** */
/* Floating point accrued exception flags                           */

function nxFlag() -> bits(5) = 0b_00001
function ufFlag() -> bits(5) = 0b_00010
function ofFlag() -> bits(5) = 0b_00100
function dzFlag() -> bits(5) = 0b_01000
function nvFlag() -> bits(5) = 0b_10000

/* **************************************************************** */
/* S and D value structure (sign, exponent, mantissa)               */

/* TODO: this should be a 'mapping' */
val      fsplit_S : bits(32) -> (bits(1), bits(8), bits(23))
function fsplit_S   x32 = (x32[31..31], x32[30..23], x32[22..0])

val      fmake_S  : (bits(1), bits(8), bits(23)) -> bits(32)
function fmake_S (sign, exp, mant) = sign @ exp @ mant

/* ---- Structure tests */

val      f_is_neg_inf_S : bits(32) -> bool
function f_is_neg_inf_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (sign == 0b1)
   & (exp  == ones())
   & (mant == zeros()))
}

val      f_is_neg_norm_S : bits(32) -> bool
function f_is_neg_norm_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (sign == 0b1)
   & (exp  != zeros())
   & (exp  != ones()))
}

val      f_is_neg_subnorm_S : bits(32) -> bool
function f_is_neg_subnorm_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (sign == 0b1)
   & (exp  == zeros())
   & (mant != zeros()))
}

val      f_is_neg_zero_S : bits(32) -> bool
function f_is_neg_zero_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (sign == ones())
   & (exp  == zeros())
   & (mant == zeros()))
}

val      f_is_pos_zero_S : bits(32) -> bool
function f_is_pos_zero_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (sign == zeros())
   & (exp  == zeros())
   & (mant == zeros()))
}

val      f_is_pos_subnorm_S : bits(32) -> bool
function f_is_pos_subnorm_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (sign == zeros())
   & (exp  == zeros())
   & (mant != zeros()))
}

val      f_is_pos_norm_S : bits(32) -> bool
function f_is_pos_norm_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (sign == zeros())
   & (exp  != zeros())
   & (exp  != ones()))
}

val      f_is_pos_inf_S : bits(32) -> bool
function f_is_pos_inf_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (sign == zeros())
   & (exp  == ones())
   & (mant == zeros()))
}

val      f_is_SNaN_S : bits(32) -> bool
function f_is_SNaN_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (exp == ones())
   & (mant [22] == bitzero)
   & (mant != zeros()))
}

val      f_is_QNaN_S : bits(32) -> bool
function f_is_QNaN_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (exp == ones())
   & (mant [22] == bitone))
}

/* Either QNaN or SNan */
val      f_is_NaN_S : bits(32) -> bool
function f_is_NaN_S   x32 = {
  let (sign, exp, mant) = fsplit_S (x32);
  (  (exp == ones())
   & (mant != zeros()))
}

/* **************************************************************** */
/* Help functions used in the semantic functions                    */

val      negate_S : bits(32) -> bits(32)
function negate_S (x32) = {
  let (sign, exp, mant) = fsplit_S (x32);
  let new_sign = if (sign == 0b0) then 0b1 else 0b0;
  fmake_S (new_sign, exp, mant)
}

val      feq_quiet_S : (bits(32), bits (32)) -> (bool, bits(5))
function feq_quiet_S   (v1,       v2) = {
  let (s1, e1, m1) = fsplit_S (v1);
  let (s2, e2, m2) = fsplit_S (v2);

  let v1Is0    = f_is_neg_zero_S(v1) | f_is_pos_zero_S(v1);
  let v2Is0    = f_is_neg_zero_S(v2) | f_is_pos_zero_S(v2);

  let result = ((v1 == v2) | (v1Is0 & v2Is0));

  let fflags = if   (f_is_SNaN_S(v1) | f_is_SNaN_S(v2))
               then nvFlag()
               else zeros();

  (result, fflags)
}

val      flt_S : (bits(32), bits (32), bool) -> (bool, bits(5))
function flt_S   (v1,       v2,        is_quiet) = {
  let (s1, e1, m1) = fsplit_S (v1);
  let (s2, e2, m2) = fsplit_S (v2);

  let result : bool =
    if (s1 == 0b0) & (s2 == 0b0) then
      if   (e1 == e2)
      then unsigned (m1) < unsigned (m2)
      else unsigned (e1) < unsigned (e2)
    else if (s1 == 0b0) & (s2 == 0b1)
    then false
    else if (s1 == 0b1) & (s2 == 0b0)
    then true
    else
        if   (e1 == e2)
        then unsigned (m1) > unsigned (m2)
        else unsigned (e1) > unsigned (e2);

  let fflags = if is_quiet then
                 if   (f_is_SNaN_S(v1) | f_is_SNaN_S(v2))
                 then nvFlag()
                 else zeros()
               else
                 if   (f_is_NaN_S(v1) | f_is_NaN_S(v2))
                 then nvFlag()
                 else zeros();

  (result, fflags)
}

val      fle_S : (bits(32), bits (32), bool) -> (bool, bits(5))
function fle_S   (v1,       v2,        is_quiet) = {
  let (s1, e1, m1) = fsplit_S (v1);
  let (s2, e2, m2) = fsplit_S (v2);

  let v1Is0    = f_is_neg_zero_S(v1) | f_is_pos_zero_S(v1);
  let v2Is0    = f_is_neg_zero_S(v2) | f_is_pos_zero_S(v2);

  let result : bool =
    if (s1 == 0b0) & (s2 == 0b0) then
      if   (e1 == e2)
      then unsigned (m1) <=  unsigned (m2)
      else unsigned (e1)  <  unsigned (e2)
    else if (s1 == 0b0) & (s2 == 0b1)
    then (v1Is0 & v2Is0)                         /* Equal in this case (+0=-0) */
    else if (s1 == 0b1) & (s2 == 0b0)
    then true
    else
      if   (e1 == e2)
      then unsigned (m1) >=  unsigned (m2)
      else unsigned (e1)  >  unsigned (e2);

  let fflags = if is_quiet then
                 if   (f_is_SNaN_S(v1) | f_is_SNaN_S(v2))
                 then nvFlag()
                 else zeros()
               else
                 if   (f_is_NaN_S(v1) | f_is_NaN_S(v2))
                 then nvFlag()
                 else zeros();

  (result, fflags)
}

/* **************************************************************** */
/* Helper functions for 'encdec()'                                  */

function haveSingleFPU() -> bool = haveFExt() | haveZfinx()

/* ****************************************************************** */
/* Floating-point loads                                               */

/* AST */
/* FLH, FLW and FLD; H/W/D is encoded in 'word_width' */

union clause ast = LOAD_FP : (bits(12), regidx, regidx, word_width)

/* AST <-> Binary encoding ================================ */

mapping clause encdec = LOAD_FP(imm, rs1, rd, HALF)          if haveZfh()
                    <-> imm @ rs1 @ 0b001 @ rd @ 0b000_0111  if haveZfh()

mapping clause encdec = LOAD_FP(imm, rs1, rd, WORD)          if haveFExt()
                    <-> imm @ rs1 @ 0b010 @ rd @ 0b000_0111  if haveFExt()

mapping clause encdec = LOAD_FP(imm, rs1, rd, DOUBLE)        if haveDExt()
                    <-> imm @ rs1 @ 0b011 @ rd @ 0b000_0111  if haveDExt()

/* Execution semantics ================================ */

val process_fload64 : (regidx, xlenbits, MemoryOpResult(bits(64)))
                      -> Retired
function process_fload64(rd, addr, value) =
  if   sizeof(flen) == 64
  then match value {
         MemValue(result) => { F(rd) = result; RETIRE_SUCCESS },
         MemException(e)  => { handle_mem_exception(addr, e); RETIRE_FAIL }
       }
  else {
    /* should not get here */
    RETIRE_FAIL
  }

val process_fload32 : (regidx, xlenbits, MemoryOpResult(bits(32)))
                      -> Retired
function process_fload32(rd, addr, value) =
  match value {
    MemValue(result) => { F(rd) = nan_box(result); RETIRE_SUCCESS },
    MemException(e)  => { handle_mem_exception(addr, e); RETIRE_FAIL }
  }

val process_fload16 : (regidx, xlenbits, MemoryOpResult(bits(16)))
                      -> Retired
function process_fload16(rd, addr, value) =
  match value {
    MemValue(result) => { F(rd) = nan_box(result); RETIRE_SUCCESS },
    MemException(e)  => { handle_mem_exception(addr, e); RETIRE_FAIL }
  }

function clause execute(LOAD_FP(imm, rs1, rd, width)) = {
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
        TR_Address(addr, _) => {
          let (aq, rl, res) = (false, false, false);
          match (width) {
            BYTE => { handle_illegal(); RETIRE_FAIL },
            HALF =>
               process_fload16(rd, vaddr, mem_read(Read(Data), addr, 2, aq, rl, res)),
            WORD =>
               process_fload32(rd, vaddr, mem_read(Read(Data), addr, 4, aq, rl, res)),
            DOUBLE if sizeof(flen) >= 64 =>
               process_fload64(rd, vaddr, mem_read(Read(Data), addr, 8, aq, rl, res)),
            _ => report_invalid_width(__FILE__, __LINE__, width, "floating point load"),
          }
        }
      }
  }
}

/* AST -> Assembly notation ================================ */

mapping clause assembly = LOAD_FP(imm, rs1, rd, width)
                      <-> "fl" ^ size_mnemonic(width)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ hex_bits_12(imm)
                          ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"

/* ****************************************************************** */
/* Floating-point stores                                              */

/* AST */
/* FSH, FSW and FSD; H/W/D is encoded in 'word_width' */

union clause ast = STORE_FP : (bits(12), regidx, regidx, word_width)

/* AST <-> Binary encoding ================================ */

mapping clause encdec = STORE_FP(imm7 @ imm5, rs2, rs1, HALF)                             if haveZfh()
                    <-> imm7 : bits(7) @ rs2 @ rs1 @ 0b001 @ imm5 : bits(5) @ 0b010_0111  if haveZfh()

mapping clause encdec = STORE_FP(imm7 @ imm5, rs2, rs1, WORD)                             if haveFExt()
                    <-> imm7 : bits(7) @ rs2 @ rs1 @ 0b010 @ imm5 : bits(5) @ 0b010_0111  if haveFExt()

mapping clause encdec = STORE_FP(imm7 @ imm5, rs2, rs1, DOUBLE)                           if haveDExt()
                    <-> imm7 : bits(7) @ rs2 @ rs1 @ 0b011 @ imm5 : bits(5) @ 0b010_0111  if haveDExt()

/* Execution semantics ================================ */

val process_fstore : (xlenbits, MemoryOpResult(bool)) -> Retired
function process_fstore(vaddr, value) =
  match value {
    MemValue(true)  => { RETIRE_SUCCESS },
    MemValue(false) => { internal_error(__FILE__, __LINE__, "store got false from mem_write_value") },
    MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
  }

function clause execute (STORE_FP(imm, rs2, rs1, width)) = {
  let offset : xlenbits = sign_extend(imm);
  let (aq, rl, con) = (false, false, false);
  /* Get the address, X(rs1) + offset.
     Some extensions perform additional checks on address validity. */
  match ext_data_get_addr(rs1, offset, Write(Data), width) {
    Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); RETIRE_FAIL },
    Ext_DataAddr_OK(vaddr) =>
      if   check_misaligned(vaddr, width)
      then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); RETIRE_FAIL }
      else match translateAddr(vaddr, Write(Data)) {
        TR_Failure(e, _)    => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
        TR_Address(addr, _) => {
          let eares : MemoryOpResult(unit) = match width {
            BYTE   => MemValue () /* bogus placeholder for illegal size */,
            HALF   => mem_write_ea(addr, 2, aq, rl, false),
            WORD   => mem_write_ea(addr, 4, aq, rl, false),
            DOUBLE => mem_write_ea(addr, 8, aq, rl, false)
          };
          match (eares) {
            MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
            MemValue(_) => {
              let rs2_val = F(rs2);
              match (width) {
                BYTE => { handle_illegal(); RETIRE_FAIL },
                HALF => process_fstore (vaddr, mem_write_value(addr, 2, rs2_val[15..0], aq, rl, con)),
                WORD => process_fstore (vaddr, mem_write_value(addr, 4, rs2_val[31..0], aq, rl, con)),
                DOUBLE if sizeof(flen) >= 64 =>
                  process_fstore (vaddr, mem_write_value(addr, 8, rs2_val, aq, rl, con)),
                _ => report_invalid_width(__FILE__, __LINE__, width, "floating point store"),
              };
            }
          }
        }
      }
  }
}

/* AST -> Assembly notation ================================ */

mapping clause assembly = STORE_FP(imm, rs2, rs1, width)
                      <-> "fs" ^ size_mnemonic(width)
                          ^ spc() ^ freg_name(rs2)
                          ^ sep() ^ hex_bits_12(imm)
                          ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"

/* ****************************************************************** */
/* Fused multiply-add */

/* AST */

union clause ast = F_MADD_TYPE_S : (regidx, regidx, regidx, rounding_mode, regidx, f_madd_op_S)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_MADD_TYPE_S(rs3, rs2, rs1, rm, rd, FMADD_S)                         if haveSingleFPU()
<-> rs3 @ 0b00 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_0011  if haveSingleFPU()

mapping clause encdec =
    F_MADD_TYPE_S(rs3, rs2, rs1, rm, rd, FMSUB_S)                         if haveSingleFPU()
<-> rs3 @ 0b00 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_0111  if haveSingleFPU()

mapping clause encdec =
    F_MADD_TYPE_S(rs3, rs2, rs1, rm, rd, FNMSUB_S)                        if haveSingleFPU()
<-> rs3 @ 0b00 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_1011  if haveSingleFPU()

mapping clause encdec =
    F_MADD_TYPE_S(rs3, rs2, rs1, rm, rd, FNMADD_S)                        if haveSingleFPU()
<-> rs3 @ 0b00 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_1111  if haveSingleFPU()

/* Execution semantics ================================ */

function clause execute (F_MADD_TYPE_S(rs3, rs2, rs1, rm, rd, op)) = {
  let rs1_val_32b = F_or_X_S(rs1);
  let rs2_val_32b = F_or_X_S(rs2);
  let rs3_val_32b = F_or_X_S(rs3);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_32b) : (bits(5), bits(32)) =
        match op {
          FMADD_S  => riscv_f32MulAdd (rm_3b, rs1_val_32b, rs2_val_32b, rs3_val_32b),
          FMSUB_S  => riscv_f32MulAdd (rm_3b, rs1_val_32b, rs2_val_32b, negate_S (rs3_val_32b)),
          FNMSUB_S => riscv_f32MulAdd (rm_3b, negate_S (rs1_val_32b), rs2_val_32b, rs3_val_32b),
          FNMADD_S => riscv_f32MulAdd (rm_3b, negate_S (rs1_val_32b), rs2_val_32b, negate_S (rs3_val_32b))
        };
      accrue_fflags(fflags);
      F_or_X_S(rd) = rd_val_32b;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_madd_type_mnemonic_S : f_madd_op_S <-> string = {
    FMADD_S  <-> "fmadd.s",
    FMSUB_S  <-> "fmsub.s",
    FNMSUB_S <-> "fnmsub.s",
    FNMADD_S <-> "fnmadd.s"
}

mapping clause assembly = F_MADD_TYPE_S(rs3, rs2, rs1, rm, rd, op)
                      <-> f_madd_type_mnemonic_S(op)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)
                          ^ sep() ^ freg_or_reg_name(rs3)
                          ^ sep() ^ frm_mnemonic(rm)

/* ****************************************************************** */
/* Binary ops with rounding mode */

/* AST */

union clause ast = F_BIN_RM_TYPE_S : (regidx, regidx, rounding_mode, regidx, f_bin_rm_op_S)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_BIN_RM_TYPE_S(rs2, rs1, rm, rd, FADD_S)                             if haveSingleFPU()
<-> 0b000_0000 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec =
    F_BIN_RM_TYPE_S(rs2, rs1, rm, rd, FSUB_S)                             if haveSingleFPU()
<-> 0b000_0100 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec =
    F_BIN_RM_TYPE_S(rs2, rs1, rm, rd, FMUL_S)                             if haveSingleFPU()
<-> 0b000_1000 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec =
    F_BIN_RM_TYPE_S(rs2, rs1, rm, rd, FDIV_S)                             if haveSingleFPU()
<-> 0b000_1100 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU()

/* Execution semantics ================================ */

function clause execute (F_BIN_RM_TYPE_S(rs2, rs1, rm, rd, op)) = {
  let rs1_val_32b = F_or_X_S(rs1);
  let rs2_val_32b = F_or_X_S(rs2);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_32b) : (bits(5), bits(32)) = match op {
        FADD_S  => riscv_f32Add (rm_3b, rs1_val_32b, rs2_val_32b),
        FSUB_S  => riscv_f32Sub (rm_3b, rs1_val_32b, rs2_val_32b),
        FMUL_S  => riscv_f32Mul (rm_3b, rs1_val_32b, rs2_val_32b),
        FDIV_S  => riscv_f32Div (rm_3b, rs1_val_32b, rs2_val_32b)
      };
      accrue_fflags(fflags);
      F_or_X_S(rd) = rd_val_32b;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_bin_rm_type_mnemonic_S : f_bin_rm_op_S <-> string = {
  FADD_S  <-> "fadd.s",
  FSUB_S  <-> "fsub.s",
  FMUL_S  <-> "fmul.s",
  FDIV_S  <-> "fdiv.s"
}

mapping clause assembly = F_BIN_RM_TYPE_S(rs2, rs1, rm, rd, op)
                      <-> f_bin_rm_type_mnemonic_S(op)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)
                          ^ sep() ^ frm_mnemonic(rm)

/* ****************************************************************** */
/* Unary with rounding mode */

/* AST */

union clause ast = F_UN_RM_TYPE_S : (regidx, rounding_mode, regidx, f_un_rm_op_S)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_UN_RM_TYPE_S(rs1, rm, rd, FSQRT_S)                                      if haveSingleFPU()
<-> 0b010_1100 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec =
    F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_W_S)                                     if haveSingleFPU()
<-> 0b110_0000 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec =
    F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_WU_S)                                    if haveSingleFPU()
<-> 0b110_0000 @ 0b00001 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec =
    F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_W)                                     if haveSingleFPU()
<-> 0b110_1000 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec =
    F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_WU)                                    if haveSingleFPU()
<-> 0b110_1000 @ 0b00001 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU()

/* F instructions, RV64 only */

mapping clause encdec =
    F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_L_S)                                     if haveSingleFPU() & sizeof(xlen) >= 64
<-> 0b110_0000 @ 0b00010 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU() & sizeof(xlen) >= 64

mapping clause encdec =
    F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_LU_S)                                    if haveSingleFPU() & sizeof(xlen) >= 64
<-> 0b110_0000 @ 0b00011 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU() & sizeof(xlen) >= 64

mapping clause encdec =
    F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_L)                                     if haveSingleFPU() & sizeof(xlen) >= 64
<-> 0b110_1000 @ 0b00010 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU() & sizeof(xlen) >= 64

mapping clause encdec =
    F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_LU)                                    if haveSingleFPU() & sizeof(xlen) >= 64
<-> 0b110_1000 @ 0b00011 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveSingleFPU() & sizeof(xlen) >= 64

/* Execution semantics ================================ */

function clause execute (F_UN_RM_TYPE_S(rs1, rm, rd, FSQRT_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_S) = riscv_f32Sqrt   (rm_3b, rs1_val_S);

      accrue_fflags(fflags);
      F_or_X_S(rd) = rd_val_S;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_W_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_W) = riscv_f32ToI32 (rm_3b, rs1_val_S);

      accrue_fflags(fflags);
      X(rd) = sign_extend (rd_val_W);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_WU_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_WU) = riscv_f32ToUi32 (rm_3b, rs1_val_S);

      accrue_fflags(fflags);
      X(rd) = sign_extend (rd_val_WU);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_W)) = {
  let rs1_val_W = X(rs1, rs_1) [31..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_S) = riscv_i32ToF32 (rm_3b, rs1_val_W);

      accrue_fflags(fflags);
      F_or_X_S(rd) = rd_val_S;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_WU)) = {
  let rs1_val_WU = X(rs1, rs_1) [31..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_S) = riscv_ui32ToF32 (rm_3b, rs1_val_WU);

      accrue_fflags(fflags);
      F_or_X_S(rd) = rd_val_S;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_L_S)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_S = F_or_X_S(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_L) = riscv_f32ToI64 (rm_3b, rs1_val_S);

      accrue_fflags(fflags);
      X(rd) = sign_extend(rd_val_L);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_LU_S)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_S = F_or_X_S(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_LU) = riscv_f32ToUi64 (rm_3b, rs1_val_S);

      accrue_fflags(fflags);
      X(rd) = sign_extend(rd_val_LU);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_L)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_L = X(rs1, rs_1)[63..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_S) = riscv_i64ToF32 (rm_3b, rs1_val_L);

      accrue_fflags(fflags);
      F_or_X_S(rd) = rd_val_S;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_LU)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_LU = X(rs1, rs_1)[63..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_S) = riscv_ui64ToF32 (rm_3b, rs1_val_LU);

      accrue_fflags(fflags);
      F_or_X_S(rd) = rd_val_S;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_un_rm_type_mnemonic_S : f_un_rm_op_S <-> string = {
    FSQRT_S   <-> "fsqrt.s",
    FCVT_W_S  <-> "fcvt.w.s",
    FCVT_WU_S <-> "fcvt.wu.s",
    FCVT_S_W  <-> "fcvt.s.w",
    FCVT_S_WU <-> "fcvt.s.wu",

    FCVT_L_S  <-> "fcvt.l.s",
    FCVT_LU_S <-> "fcvt.lu.s",
    FCVT_S_L  <-> "fcvt.s.l",
    FCVT_S_LU <-> "fcvt.s.lu"
}

mapping clause assembly = F_UN_RM_TYPE_S(rs1, rm, rd, FSQRT_S)
                      <-> f_un_rm_type_mnemonic_S(FSQRT_S)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_W_S)
                      <-> f_un_rm_type_mnemonic_S(FCVT_W_S)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_WU_S)
                      <-> f_un_rm_type_mnemonic_S(FCVT_WU_S)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_W)
                      <-> f_un_rm_type_mnemonic_S(FCVT_S_W)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_WU)
                      <-> f_un_rm_type_mnemonic_S(FCVT_S_WU)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_L_S)
                      <-> f_un_rm_type_mnemonic_S(FCVT_L_S)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_LU_S)
                      <-> f_un_rm_type_mnemonic_S(FCVT_LU_S)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_L)
                      <-> f_un_rm_type_mnemonic_S(FCVT_S_L)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_S(rs1, rm, rd, FCVT_S_LU)
                      <-> f_un_rm_type_mnemonic_S(FCVT_S_LU)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)


/* ****************************************************************** */
/* Binary, no rounding mode */

/* AST */

union clause ast = F_BIN_TYPE_S : (regidx, regidx, regidx, f_bin_op_S)

/* AST <-> Binary encoding ================================ */

mapping clause encdec = F_BIN_TYPE_S(rs2, rs1, rd, FSGNJ_S)               if haveSingleFPU()
                    <-> 0b001_0000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec = F_BIN_TYPE_S(rs2, rs1, rd, FSGNJN_S)              if haveSingleFPU()
                    <-> 0b001_0000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec = F_BIN_TYPE_S(rs2, rs1, rd, FSGNJX_S)              if haveSingleFPU()
                    <-> 0b001_0000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec = F_BIN_TYPE_S(rs2, rs1, rd, FMIN_S)                if haveSingleFPU()
                    <-> 0b001_0100 @ rs2 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec = F_BIN_TYPE_S(rs2, rs1, rd, FMAX_S)                if haveSingleFPU()
                    <-> 0b001_0100 @ rs2 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec = F_BIN_TYPE_S(rs2, rs1, rd, FEQ_S)                 if haveSingleFPU()
                    <-> 0b101_0000 @ rs2 @ rs1 @ 0b010 @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec = F_BIN_TYPE_S(rs2, rs1, rd, FLT_S)                 if haveSingleFPU()
                    <-> 0b101_0000 @ rs2 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec = F_BIN_TYPE_S(rs2, rs1, rd, FLE_S)                 if haveSingleFPU()
                    <-> 0b101_0000 @ rs2 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveSingleFPU()

/* Execution semantics ================================ */

function clause execute (F_BIN_TYPE_S(rs2, rs1, rd, FSGNJ_S)) = {
  let rs1_val_S    = F_or_X_S(rs1);
  let rs2_val_S    = F_or_X_S(rs2);
  let (s1, e1, m1) = fsplit_S (rs1_val_S);
  let (s2, e2, m2) = fsplit_S (rs2_val_S);
  let rd_val_S     = fmake_S (s2, e1, m1);

  F_or_X_S(rd) = rd_val_S;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_S(rs2, rs1, rd, FSGNJN_S)) = {
  let rs1_val_S    = F_or_X_S(rs1);
  let rs2_val_S    = F_or_X_S(rs2);
  let (s1, e1, m1) = fsplit_S (rs1_val_S);
  let (s2, e2, m2) = fsplit_S (rs2_val_S);
  let rd_val_S     = fmake_S (0b1 ^ s2, e1, m1);

  F_or_X_S(rd) = rd_val_S;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_S(rs2, rs1, rd, FSGNJX_S)) = {
  let rs1_val_S    = F_or_X_S(rs1);
  let rs2_val_S    = F_or_X_S(rs2);
  let (s1, e1, m1) = fsplit_S (rs1_val_S);
  let (s2, e2, m2) = fsplit_S (rs2_val_S);
  let rd_val_S     = fmake_S (s1 ^ s2, e1, m1);

  F_or_X_S(rd) = rd_val_S;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_S(rs2, rs1, rd, FMIN_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  let rs2_val_S = F_or_X_S(rs2);

  let is_quiet  = true;
  let (rs1_lt_rs2, fflags) = fle_S (rs1_val_S, rs2_val_S, is_quiet);

  let rd_val_S  = if      (f_is_NaN_S(rs1_val_S) & f_is_NaN_S(rs2_val_S))           then canonical_NaN_S()
                  else if f_is_NaN_S(rs1_val_S)                                     then rs2_val_S
                  else if f_is_NaN_S(rs2_val_S)                                     then rs1_val_S
                  else if (f_is_neg_zero_S(rs1_val_S) & f_is_pos_zero_S(rs2_val_S)) then rs1_val_S
                  else if (f_is_neg_zero_S(rs2_val_S) & f_is_pos_zero_S(rs1_val_S)) then rs2_val_S
                  else if rs1_lt_rs2                                                then rs1_val_S
                  else /* (not rs1_lt_rs2) */                                            rs2_val_S;

  accrue_fflags(fflags);
  F_or_X_S(rd) = rd_val_S;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_S(rs2, rs1, rd, FMAX_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  let rs2_val_S = F_or_X_S(rs2);

  let is_quiet  = true;
  let (rs2_lt_rs1, fflags) = fle_S (rs2_val_S, rs1_val_S, is_quiet);

  let rd_val_S  = if      (f_is_NaN_S(rs1_val_S) & f_is_NaN_S(rs2_val_S))           then canonical_NaN_S()
                  else if f_is_NaN_S(rs1_val_S)                                     then rs2_val_S
                  else if f_is_NaN_S(rs2_val_S)                                     then rs1_val_S
                  else if (f_is_neg_zero_S(rs1_val_S) & f_is_pos_zero_S(rs2_val_S)) then rs2_val_S
                  else if (f_is_neg_zero_S(rs2_val_S) & f_is_pos_zero_S(rs1_val_S)) then rs1_val_S
                  else if rs2_lt_rs1                                                then rs1_val_S
                  else /* (not rs2_lt_rs1) */                                            rs2_val_S;

  accrue_fflags(fflags);
  F_or_X_S(rd) = rd_val_S;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_S(rs2, rs1, rd, FEQ_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  let rs2_val_S = F_or_X_S(rs2);

  let (fflags, rd_val) : (bits_fflags, bool) =
      riscv_f32Eq (rs1_val_S, rs2_val_S);

  accrue_fflags(fflags);
  X(rd) = zero_extend(bool_to_bits(rd_val));
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_S(rs2, rs1, rd, FLT_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  let rs2_val_S = F_or_X_S(rs2);

  let (fflags, rd_val) : (bits_fflags, bool) =
      riscv_f32Lt (rs1_val_S, rs2_val_S);

  accrue_fflags(fflags);
  X(rd) = zero_extend(bool_to_bits(rd_val));
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_S(rs2, rs1, rd, FLE_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  let rs2_val_S = F_or_X_S(rs2);

  let (fflags, rd_val) : (bits_fflags, bool) =
      riscv_f32Le (rs1_val_S, rs2_val_S);

  accrue_fflags(fflags);
  X(rd) = zero_extend(bool_to_bits(rd_val));
  RETIRE_SUCCESS
}

/* AST -> Assembly notation ================================ */

mapping f_bin_type_mnemonic_S : f_bin_op_S <-> string = {
    FSGNJ_S  <-> "fsgnj.s",
    FSGNJN_S <-> "fsgnjn.s",
    FSGNJX_S <-> "fsgnjx.s",
    FMIN_S   <-> "fmin.s",
    FMAX_S   <-> "fmax.s",
    FEQ_S    <-> "feq.s",
    FLT_S    <-> "flt.s",
    FLE_S    <-> "fle.s"
}

mapping clause assembly = F_BIN_TYPE_S(rs2, rs1, rd, FSGNJ_S)
                      <-> f_bin_type_mnemonic_S(FSGNJ_S)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_S(rs2, rs1, rd, FSGNJN_S)
                      <-> f_bin_type_mnemonic_S(FSGNJN_S)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_S(rs2, rs1, rd, FSGNJX_S)
                      <-> f_bin_type_mnemonic_S(FSGNJX_S)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_S(rs2, rs1, rd, FMIN_S)
                      <-> f_bin_type_mnemonic_S(FMIN_S)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_S(rs2, rs1, rd, FMAX_S)
                      <-> f_bin_type_mnemonic_S(FMAX_S)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_S(rs2, rs1, rd, FEQ_S)
                      <-> f_bin_type_mnemonic_S(FEQ_S)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_S(rs2, rs1, rd, FLT_S)
                      <-> f_bin_type_mnemonic_S(FLT_S)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_S(rs2, rs1, rd, FLE_S)
                      <-> f_bin_type_mnemonic_S(FLE_S)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

/* ****************************************************************** */
/* Unary, no rounding mode */

union clause ast = F_UN_TYPE_S : (regidx, regidx, f_un_op_S)

/* AST <-> Binary encoding ================================ */

mapping clause encdec = F_UN_TYPE_S(rs1, rd, FCLASS_S)                        if haveSingleFPU()
                    <-> 0b111_0000 @ 0b00000 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveSingleFPU()

mapping clause encdec = F_UN_TYPE_S(rs1, rd, FMV_X_W)                         if haveFExt()
                    <-> 0b111_0000 @ 0b00000 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveFExt()

mapping clause encdec = F_UN_TYPE_S(rs1, rd, FMV_W_X)                         if haveFExt()
                    <-> 0b111_1000 @ 0b00000 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveFExt()

/* Execution semantics ================================ */

function clause execute (F_UN_TYPE_S(rs1, rd, FCLASS_S)) = {
  let rs1_val_S = F_or_X_S(rs1);

  let rd_val_10b : bits (10) =
    if      f_is_neg_inf_S     (rs1_val_S) then 0b_00_0000_0001
    else if f_is_neg_norm_S    (rs1_val_S) then 0b_00_0000_0010
    else if f_is_neg_subnorm_S (rs1_val_S) then 0b_00_0000_0100
    else if f_is_neg_zero_S    (rs1_val_S) then 0b_00_0000_1000
    else if f_is_pos_zero_S    (rs1_val_S) then 0b_00_0001_0000
    else if f_is_pos_subnorm_S (rs1_val_S) then 0b_00_0010_0000
    else if f_is_pos_norm_S    (rs1_val_S) then 0b_00_0100_0000
    else if f_is_pos_inf_S     (rs1_val_S) then 0b_00_1000_0000
    else if f_is_SNaN_S        (rs1_val_S) then 0b_01_0000_0000
    else if f_is_QNaN_S        (rs1_val_S) then 0b_10_0000_0000
    else zeros();

  X(rd) = zero_extend (rd_val_10b);
  RETIRE_SUCCESS
}

function clause execute (F_UN_TYPE_S(rs1, rd, FMV_X_W)) = {
  let rs1_val_S            = F(rs1)[31..0];
  let rd_val_X  : xlenbits = sign_extend(rs1_val_S);
  X(rd) = rd_val_X;
  RETIRE_SUCCESS
}

function clause execute (F_UN_TYPE_S(rs1, rd, FMV_W_X)) = {
  let rs1_val_X            = X(rs1, rs_1);
  let rd_val_S             = rs1_val_X [31..0];
  F(rd) = nan_box (rd_val_S);
  RETIRE_SUCCESS
}

/* AST -> Assembly notation ================================ */

mapping f_un_type_mnemonic_S : f_un_op_S <-> string = {
    FMV_X_W  <-> "fmv.x.w",
    FCLASS_S <-> "fclass.s",
    FMV_W_X  <-> "fmv.w.x"
}

mapping clause assembly = F_UN_TYPE_S(rs1, rd, FMV_X_W)
                      <-> f_un_type_mnemonic_S(FMV_X_W)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_name(rs1)

mapping clause assembly = F_UN_TYPE_S(rs1, rd, FMV_W_X)
                      <-> f_un_type_mnemonic_S(FMV_W_X)
                          ^ spc() ^ freg_name(rd)
                          ^ sep() ^ reg_name(rs1)

mapping clause assembly = F_UN_TYPE_S(rs1, rd, FCLASS_S)
                      <-> f_un_type_mnemonic_S(FCLASS_S)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)

/* ****************************************************************** */
