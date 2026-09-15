/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* **************************************************************** */
/* This file specifies the instructions in the Zfh extension        */
/* (half precision floating point).                                 */

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

val      fsplit_H : bits(16) -> (bits(1), bits(5), bits(10))
function fsplit_H   (xf16) = (xf16[15..15], xf16[14..10], xf16[9..0])

val      fmake_H  : (bits(1), bits(5), bits(10)) -> bits(16)
function fmake_H (sign, exp, mant) = sign @ exp @ mant

val      negate_H : bits(16) -> bits(16)
function negate_H (xf16) = {
  let (sign, exp, mant) = fsplit_H (xf16);
  let new_sign = if (sign == 0b0) then 0b1 else 0b0;
  fmake_H (new_sign, exp, mant)
}

val      f_is_neg_inf_H : bits(16) -> bool
function f_is_neg_inf_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (sign == 0b1)
   & (exp  == ones())
   & (mant == zeros()))
}

val      f_is_neg_norm_H : bits(16) -> bool
function f_is_neg_norm_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (sign == 0b1)
   & (exp  != zeros())
   & (exp  != ones()))
}

val      f_is_neg_subnorm_H : bits(16) -> bool
function f_is_neg_subnorm_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (sign == 0b1)
   & (exp  == zeros())
   & (mant != zeros()))
}

val      f_is_pos_subnorm_H : bits(16) -> bool
function f_is_pos_subnorm_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (sign == zeros())
   & (exp  == zeros())
   & (mant != zeros()))
}

val      f_is_pos_norm_H : bits(16) -> bool
function f_is_pos_norm_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (sign == zeros())
   & (exp  != zeros())
   & (exp  != ones()))
}

val      f_is_pos_inf_H : bits(16) -> bool
function f_is_pos_inf_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (sign == zeros())
   & (exp  == ones())
   & (mant == zeros()))
}

val      f_is_neg_zero_H : bits(16) -> bool
function f_is_neg_zero_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (sign == ones())
   & (exp  == zeros())
   & (mant == zeros()))
}

val      f_is_pos_zero_H : bits(16) -> bool
function f_is_pos_zero_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (sign == zeros())
   & (exp  == zeros())
   & (mant == zeros()))
}

val      f_is_SNaN_H : bits(16) -> bool
function f_is_SNaN_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (exp == ones())
   & (mant [9] == bitzero)
   & (mant != zeros()))
}

val      f_is_QNaN_H : bits(16) -> bool
function f_is_QNaN_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (exp == ones())
   & (mant [9] == bitone))
}

/* Either QNaN or SNan */
val      f_is_NaN_H : bits(16) -> bool
function f_is_NaN_H   xf16 = {
  let (sign, exp, mant) = fsplit_H (xf16);
  (  (exp == ones())
   & (mant != zeros()))
}

val      fle_H : (bits(16), bits (16), bool) -> (bool, bits(5))
function fle_H   (v1,       v2,        is_quiet) = {
  let (s1, e1, m1) = fsplit_H (v1);
  let (s2, e2, m2) = fsplit_H (v2);

  let v1Is0    = f_is_neg_zero_H(v1) | f_is_pos_zero_H(v1);
  let v2Is0    = f_is_neg_zero_H(v2) | f_is_pos_zero_H(v2);

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
                 if   (f_is_SNaN_H(v1) | f_is_SNaN_H(v2))
                 then nvFlag()
                 else zeros()
               else
                 if   (f_is_NaN_H(v1) | f_is_NaN_H(v2))
                 then nvFlag()
                 else zeros();

  (result, fflags)
}

/* **************************************************************** */
/* Helper functions for 'encdec()'                                  */

function haveHalfFPU() -> bool = haveZfh() | haveZhinx()

/* ****************************************************************** */
/* Floating-point loads                                               */
/* These are defined in: riscv_insts_fext.sail                        */

/* ****************************************************************** */
/* Floating-point stores                                              */
/* These are defined in: riscv_insts_fext.sail                        */

/* Binary ops with rounding mode */

/* AST */

union clause ast = F_BIN_RM_TYPE_H : (regidx, regidx, rounding_mode, regidx, f_bin_rm_op_H)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_BIN_RM_TYPE_H(rs2, rs1, rm, rd, FADD_H)                             if haveHalfFPU()
<-> 0b000_0010 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_BIN_RM_TYPE_H(rs2, rs1, rm, rd, FSUB_H)                             if haveHalfFPU()
<-> 0b000_0110 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_BIN_RM_TYPE_H(rs2, rs1, rm, rd, FMUL_H)                             if haveHalfFPU()
<-> 0b000_1010 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_BIN_RM_TYPE_H(rs2, rs1, rm, rd, FDIV_H)                             if haveHalfFPU()
<-> 0b000_1110 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

/* Execution semantics ================================ */

function clause execute (F_BIN_RM_TYPE_H(rs2, rs1, rm, rd, op)) = {
  let rs1_val_16b = F_or_X_H(rs1);
  let rs2_val_16b = F_or_X_H(rs2);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_16b) : (bits(5), bits(16)) = match op {
        FADD_H  => riscv_f16Add (rm_3b, rs1_val_16b, rs2_val_16b),
        FSUB_H  => riscv_f16Sub (rm_3b, rs1_val_16b, rs2_val_16b),
        FMUL_H  => riscv_f16Mul (rm_3b, rs1_val_16b, rs2_val_16b),
        FDIV_H  => riscv_f16Div (rm_3b, rs1_val_16b, rs2_val_16b)
      };
      accrue_fflags(fflags);
      F_or_X_H(rd) = rd_val_16b;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_bin_rm_type_mnemonic_H : f_bin_rm_op_H <-> string = {
  FADD_H  <-> "fadd.h",
  FSUB_H  <-> "fsub.h",
  FMUL_H  <-> "fmul.h",
  FDIV_H  <-> "fdiv.h"
}

mapping clause assembly = F_BIN_RM_TYPE_H(rs2, rs1, rm, rd, op)
                      <-> f_bin_rm_type_mnemonic_H(op)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)
                          ^ sep() ^ frm_mnemonic(rm)

/* ****************************************************************** */
/* Fused multiply-add */

/* AST */

union clause ast = F_MADD_TYPE_H : (regidx, regidx, regidx, rounding_mode, regidx, f_madd_op_H)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_MADD_TYPE_H(rs3, rs2, rs1, rm, rd, FMADD_H)                         if haveHalfFPU()
<-> rs3 @ 0b10 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_0011  if haveHalfFPU()

mapping clause encdec =
    F_MADD_TYPE_H(rs3, rs2, rs1, rm, rd, FMSUB_H)                         if haveHalfFPU()
<-> rs3 @ 0b10 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_0111  if haveHalfFPU()

mapping clause encdec =
    F_MADD_TYPE_H(rs3, rs2, rs1, rm, rd, FNMSUB_H)                        if haveHalfFPU()
<-> rs3 @ 0b10 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_1011  if haveHalfFPU()

mapping clause encdec =
    F_MADD_TYPE_H(rs3, rs2, rs1, rm, rd, FNMADD_H)                        if haveHalfFPU()
<-> rs3 @ 0b10 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_1111  if haveHalfFPU()

/* Execution semantics ================================ */

function clause execute (F_MADD_TYPE_H(rs3, rs2, rs1, rm, rd, op)) = {
  let rs1_val_16b = F_or_X_H(rs1);
  let rs2_val_16b = F_or_X_H(rs2);
  let rs3_val_16b = F_or_X_H(rs3);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_16b) : (bits(5), bits(16)) =
        match op {
          FMADD_H  => riscv_f16MulAdd (rm_3b, rs1_val_16b, rs2_val_16b, rs3_val_16b),
          FMSUB_H  => riscv_f16MulAdd (rm_3b, rs1_val_16b, rs2_val_16b, negate_H (rs3_val_16b)),
          FNMSUB_H => riscv_f16MulAdd (rm_3b, negate_H (rs1_val_16b), rs2_val_16b, rs3_val_16b),
          FNMADD_H => riscv_f16MulAdd (rm_3b, negate_H (rs1_val_16b), rs2_val_16b, negate_H (rs3_val_16b))
        };
      accrue_fflags(fflags);
      F_or_X_H(rd) = rd_val_16b;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_madd_type_mnemonic_H : f_madd_op_H <-> string = {
    FMADD_H  <-> "fmadd.h",
    FMSUB_H  <-> "fmsub.h",
    FNMSUB_H <-> "fnmsub.h",
    FNMADD_H <-> "fnmadd.h"
}

mapping clause assembly = F_MADD_TYPE_H(rs3, rs2, rs1, rm, rd, op)
                      <-> f_madd_type_mnemonic_H(op)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)
                          ^ sep() ^ freg_or_reg_name(rs3)
                          ^ sep() ^ frm_mnemonic(rm)

/* ****************************************************************** */
/* Binary, no rounding mode */

/* AST */

union clause ast = F_BIN_TYPE_H : (regidx, regidx, regidx, f_bin_op_H)

/* AST <-> Binary encoding ================================ */

mapping clause encdec = F_BIN_TYPE_H(rs2, rs1, rd, FSGNJ_H)               if haveHalfFPU()
                    <-> 0b001_0010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec = F_BIN_TYPE_H(rs2, rs1, rd, FSGNJN_H)              if haveHalfFPU()
                    <-> 0b001_0010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec = F_BIN_TYPE_H(rs2, rs1, rd, FSGNJX_H)              if haveHalfFPU()
                    <-> 0b001_0010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec = F_BIN_TYPE_H(rs2, rs1, rd, FMIN_H)                if haveHalfFPU()
                    <-> 0b001_0110 @ rs2 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec = F_BIN_TYPE_H(rs2, rs1, rd, FMAX_H)                if haveHalfFPU()
                    <-> 0b001_0110 @ rs2 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec = F_BIN_TYPE_H(rs2, rs1, rd, FEQ_H)                 if haveHalfFPU()
                    <-> 0b101_0010 @ rs2 @ rs1 @ 0b010 @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec = F_BIN_TYPE_H(rs2, rs1, rd, FLT_H)                 if haveHalfFPU()
                    <-> 0b101_0010 @ rs2 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec = F_BIN_TYPE_H(rs2, rs1, rd, FLE_H)                 if haveHalfFPU()
                    <-> 0b101_0010 @ rs2 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveHalfFPU()

/* Execution semantics ================================ */

function clause execute (F_BIN_TYPE_H(rs2, rs1, rd, FSGNJ_H)) = {
  let rs1_val_H    = F_or_X_H(rs1);
  let rs2_val_H    = F_or_X_H(rs2);
  let (s1, e1, m1) = fsplit_H (rs1_val_H);
  let (s2, e2, m2) = fsplit_H (rs2_val_H);
  let rd_val_H     = fmake_H (s2, e1, m1);

  F_or_X_H(rd) = rd_val_H;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_H(rs2, rs1, rd, FSGNJN_H)) = {
  let rs1_val_H    = F_or_X_H(rs1);
  let rs2_val_H    = F_or_X_H(rs2);
  let (s1, e1, m1) = fsplit_H (rs1_val_H);
  let (s2, e2, m2) = fsplit_H (rs2_val_H);
  let rd_val_H     = fmake_H (0b1 ^ s2, e1, m1);

  F_or_X_H(rd) = rd_val_H;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_H(rs2, rs1, rd, FSGNJX_H)) = {
  let rs1_val_H    = F_or_X_H(rs1);
  let rs2_val_H    = F_or_X_H(rs2);
  let (s1, e1, m1) = fsplit_H (rs1_val_H);
  let (s2, e2, m2) = fsplit_H (rs2_val_H);
  let rd_val_H     = fmake_H (s1 ^ s2, e1, m1);

  F_or_X_H(rd) = rd_val_H;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_H(rs2, rs1, rd, FMIN_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  let rs2_val_H = F_or_X_H(rs2);

  let is_quiet  = true;
  let (rs1_lt_rs2, fflags) = fle_H (rs1_val_H, rs2_val_H, is_quiet);

  let rd_val_H  = if      (f_is_NaN_H(rs1_val_H) & f_is_NaN_H(rs2_val_H))           then canonical_NaN_H()
                  else if f_is_NaN_H(rs1_val_H)                                     then rs2_val_H
                  else if f_is_NaN_H(rs2_val_H)                                     then rs1_val_H
                  else if (f_is_neg_zero_H(rs1_val_H) & f_is_pos_zero_H(rs2_val_H)) then rs1_val_H
                  else if (f_is_neg_zero_H(rs2_val_H) & f_is_pos_zero_H(rs1_val_H)) then rs2_val_H
                  else if rs1_lt_rs2                                                then rs1_val_H
                  else /* (not rs1_lt_rs2) */                                            rs2_val_H;

  accrue_fflags(fflags);
  F_or_X_H(rd) = rd_val_H;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_H(rs2, rs1, rd, FMAX_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  let rs2_val_H = F_or_X_H(rs2);

  let is_quiet  = true;
  let (rs2_lt_rs1, fflags) = fle_H (rs2_val_H, rs1_val_H, is_quiet);

  let rd_val_H  = if      (f_is_NaN_H(rs1_val_H) & f_is_NaN_H(rs2_val_H))           then canonical_NaN_H()
                  else if f_is_NaN_H(rs1_val_H)                                     then rs2_val_H
                  else if f_is_NaN_H(rs2_val_H)                                     then rs1_val_H
                  else if (f_is_neg_zero_H(rs1_val_H) & f_is_pos_zero_H(rs2_val_H)) then rs2_val_H
                  else if (f_is_neg_zero_H(rs2_val_H) & f_is_pos_zero_H(rs1_val_H)) then rs1_val_H
                  else if rs2_lt_rs1                                                then rs1_val_H
                  else /* (not rs2_lt_rs1) */                                            rs2_val_H;

  accrue_fflags(fflags);
  F_or_X_H(rd) = rd_val_H;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_H(rs2, rs1, rd, FEQ_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  let rs2_val_H = F_or_X_H(rs2);

  let (fflags, rd_val) : (bits_fflags, bool) =
      riscv_f16Eq (rs1_val_H, rs2_val_H);

  accrue_fflags(fflags);
  X(rd) = zero_extend(bool_to_bits(rd_val));
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_H(rs2, rs1, rd, FLT_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  let rs2_val_H = F_or_X_H(rs2);

  let (fflags, rd_val) : (bits_fflags, bool) =
      riscv_f16Lt (rs1_val_H, rs2_val_H);

  accrue_fflags(fflags);
  X(rd) = zero_extend(bool_to_bits(rd_val));
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_H(rs2, rs1, rd, FLE_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  let rs2_val_H = F_or_X_H(rs2);

  let (fflags, rd_val) : (bits_fflags, bool) =
      riscv_f16Le (rs1_val_H, rs2_val_H);

  accrue_fflags(fflags);
  X(rd) = zero_extend(bool_to_bits(rd_val));
  RETIRE_SUCCESS
}

/* AST -> Assembly notation ================================ */

mapping f_bin_type_mnemonic_H : f_bin_op_H <-> string = {
    FSGNJ_H  <-> "fsgnj.h",
    FSGNJN_H <-> "fsgnjn.h",
    FSGNJX_H <-> "fsgnjx.h",
    FMIN_H   <-> "fmin.h",
    FMAX_H   <-> "fmax.h",
    FEQ_H    <-> "feq.h",
    FLT_H    <-> "flt.h",
    FLE_H    <-> "fle.h"
}

mapping clause assembly = F_BIN_TYPE_H(rs2, rs1, rd, FSGNJ_H)
                      <-> f_bin_type_mnemonic_H(FSGNJ_H)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_H(rs2, rs1, rd, FSGNJN_H)
                      <-> f_bin_type_mnemonic_H(FSGNJN_H)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_H(rs2, rs1, rd, FSGNJX_H)
                      <-> f_bin_type_mnemonic_H(FSGNJX_H)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_H(rs2, rs1, rd, FMIN_H)
                      <-> f_bin_type_mnemonic_H(FMIN_H)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_H(rs2, rs1, rd, FMAX_H)
                      <-> f_bin_type_mnemonic_H(FMAX_H)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_H(rs2, rs1, rd, FEQ_H)
                      <-> f_bin_type_mnemonic_H(FEQ_H)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_H(rs2, rs1, rd, FLT_H)
                      <-> f_bin_type_mnemonic_H(FLT_H)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_H(rs2, rs1, rd, FLE_H)
                      <-> f_bin_type_mnemonic_H(FLE_H)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

/* ****************************************************************** */
/* Unary with rounding mode */

/* AST */

union clause ast = F_UN_RM_TYPE_H : (regidx, rounding_mode, regidx, f_un_rm_op_H)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FSQRT_H)                                      if haveHalfFPU()
<-> 0b010_1110 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_W_H)                                     if haveHalfFPU()
<-> 0b110_0010 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_WU_H)                                    if haveHalfFPU()
<-> 0b110_0010 @ 0b00001 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_W)                                     if haveHalfFPU()
<-> 0b110_1010 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_WU)                                    if haveHalfFPU()
<-> 0b110_1010 @ 0b00001 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_S)                                     if haveHalfFPU()
<-> 0b010_0010 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_D)                                     if haveHalfFPU()
<-> 0b010_0010 @ 0b00001 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_S_H)                                     if haveHalfFPU()
<-> 0b010_0000 @ 0b00010 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_D_H)                                     if haveHalfFPU()
<-> 0b010_0001 @ 0b00010 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU()

// TODO:
/* FCVT_H_Q, FCVT_Q_H : Will be added with Q Extension */

/* F instructions, RV64 only */

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_L_H)                                     if haveHalfFPU() & sizeof(xlen) >= 64
<-> 0b110_0010 @ 0b00010 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU() & sizeof(xlen) >= 64

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_LU_H)                                    if haveHalfFPU() & sizeof(xlen) >= 64
<-> 0b110_0010 @ 0b00011 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU() & sizeof(xlen) >= 64

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_L)                                     if haveHalfFPU() & sizeof(xlen) >= 64
<-> 0b110_1010 @ 0b00010 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU() & sizeof(xlen) >= 64

mapping clause encdec =
    F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_LU)                                    if haveHalfFPU() & sizeof(xlen) >= 64
<-> 0b110_1010 @ 0b00011 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveHalfFPU() & sizeof(xlen) >= 64

/* Execution semantics ================================ */

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FSQRT_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_H) = riscv_f16Sqrt   (rm_3b, rs1_val_H);

      accrue_fflags(fflags);
      F_or_X_H(rd) = rd_val_H;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_W_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_W) = riscv_f16ToI32 (rm_3b, rs1_val_H);

      accrue_fflags(fflags);
      X(rd) = sign_extend (rd_val_W);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_WU_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_WU) = riscv_f16ToUi32 (rm_3b, rs1_val_H);

      accrue_fflags(fflags);
      X(rd) = sign_extend (rd_val_WU);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_W)) = {
  let rs1_val_W = X(rs1, rs_1) [31..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_H) = riscv_i32ToF16 (rm_3b, rs1_val_W);

      accrue_fflags(fflags);
      F_or_X_H(rd) = rd_val_H;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_WU)) = {
  let rs1_val_WU = X(rs1, rs_1) [31..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_H) = riscv_ui32ToF16 (rm_3b, rs1_val_WU);

      accrue_fflags(fflags);
      F_or_X_H(rd) = rd_val_H;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_H) = riscv_f32ToF16 (rm_3b, rs1_val_S);

      accrue_fflags(fflags);
      F_or_X_H(rd) = rd_val_H;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_H) = riscv_f64ToF16 (rm_3b, rs1_val_D);

      accrue_fflags(fflags);
      F_or_X_H(rd) = rd_val_H;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_S_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_S) = riscv_f16ToF32 (rm_3b, rs1_val_H);

      accrue_fflags(fflags);
      F_or_X_S(rd) = rd_val_S;
      RETIRE_SUCCESS
    }
  }
}


function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_D_H)) = {
  let rs1_val_H = F_or_X_H(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_D) = riscv_f16ToF64 (rm_3b, rs1_val_H);

      accrue_fflags(fflags);
      F_or_X_D(rd) = rd_val_D;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_L_H)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_H = F_or_X_H(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_L) = riscv_f16ToI64 (rm_3b, rs1_val_H);

      accrue_fflags(fflags);
      X(rd) = sign_extend(rd_val_L);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_LU_H)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_H = F_or_X_H(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_LU) = riscv_f16ToUi64 (rm_3b, rs1_val_H);

      accrue_fflags(fflags);
      X(rd) = sign_extend(rd_val_LU);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_L)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_L = X(rs1, rs_1)[63..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_H) = riscv_i64ToF16 (rm_3b, rs1_val_L);

      accrue_fflags(fflags);
      F_or_X_H(rd) = rd_val_H;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_LU)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_LU = X(rs1, rs_1)[63..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_H) = riscv_ui64ToF16 (rm_3b, rs1_val_LU);

      accrue_fflags(fflags);
      F_or_X_H(rd) = rd_val_H;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_un_rm_type_mnemonic_H : f_un_rm_op_H <-> string = {
    FSQRT_H   <-> "fsqrt.h",
    FCVT_W_H  <-> "fcvt.w.h",
    FCVT_WU_H <-> "fcvt.wu.h",
    FCVT_H_W  <-> "fcvt.h.w",
    FCVT_H_WU <-> "fcvt.h.wu",

    FCVT_H_S  <-> "fcvt.h.s",
    FCVT_H_D  <-> "fcvt.h.d",
    FCVT_S_H  <-> "fcvt.s.h",
    FCVT_D_H  <-> "fcvt.d.h",

    FCVT_L_H  <-> "fcvt.l.h",
    FCVT_LU_H <-> "fcvt.lu.h",
    FCVT_H_L  <-> "fcvt.h.l",
    FCVT_H_LU <-> "fcvt.h.lu"
}

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FSQRT_H)
                      <-> f_un_rm_type_mnemonic_H(FSQRT_H)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_W_H)
                      <-> f_un_rm_type_mnemonic_H(FCVT_W_H)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_WU_H)
                      <-> f_un_rm_type_mnemonic_H(FCVT_WU_H)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_W)
                      <-> f_un_rm_type_mnemonic_H(FCVT_H_W)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_WU)
                      <-> f_un_rm_type_mnemonic_H(FCVT_H_WU)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_L_H)
                      <-> f_un_rm_type_mnemonic_H(FCVT_L_H)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_LU_H)
                      <-> f_un_rm_type_mnemonic_H(FCVT_LU_H)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_L)
                      <-> f_un_rm_type_mnemonic_H(FCVT_H_L)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_LU)
                      <-> f_un_rm_type_mnemonic_H(FCVT_H_LU)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_S)
                      <-> f_un_rm_type_mnemonic_H(FCVT_H_S)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_H_D)
                      <-> f_un_rm_type_mnemonic_H(FCVT_H_D)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_S_H)
                      <-> f_un_rm_type_mnemonic_H(FCVT_S_H)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_H(rs1, rm, rd, FCVT_D_H)
                      <-> f_un_rm_type_mnemonic_H(FCVT_D_H)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

/* ****************************************************************** */
/* Unary, no rounding mode */

union clause ast = F_UN_TYPE_H : (regidx, regidx, f_un_op_H)

/* AST <-> Binary encoding ================================ */

mapping clause encdec = F_UN_TYPE_H(rs1, rd, FCLASS_H)                        if haveHalfFPU()
                    <-> 0b111_0010 @ 0b00000 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveHalfFPU()

mapping clause encdec = F_UN_TYPE_H(rs1, rd, FMV_X_H)                         if haveZfh()
                    <-> 0b111_0010 @ 0b00000 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveZfh()

mapping clause encdec = F_UN_TYPE_H(rs1, rd, FMV_H_X)                         if haveZfh()
                    <-> 0b111_1010 @ 0b00000 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveZfh()

/* Execution semantics ================================ */

function clause execute (F_UN_TYPE_H(rs1, rd, FCLASS_H)) = {
  let rs1_val_H = F_or_X_H(rs1);

  let rd_val_10b : bits (10) =
    if      f_is_neg_inf_H     (rs1_val_H) then 0b_00_0000_0001
    else if f_is_neg_norm_H    (rs1_val_H) then 0b_00_0000_0010
    else if f_is_neg_subnorm_H (rs1_val_H) then 0b_00_0000_0100
    else if f_is_neg_zero_H    (rs1_val_H) then 0b_00_0000_1000
    else if f_is_pos_zero_H    (rs1_val_H) then 0b_00_0001_0000
    else if f_is_pos_subnorm_H (rs1_val_H) then 0b_00_0010_0000
    else if f_is_pos_norm_H    (rs1_val_H) then 0b_00_0100_0000
    else if f_is_pos_inf_H     (rs1_val_H) then 0b_00_1000_0000
    else if f_is_SNaN_H        (rs1_val_H) then 0b_01_0000_0000
    else if f_is_QNaN_H        (rs1_val_H) then 0b_10_0000_0000
    else zeros();

  X(rd) = zero_extend (rd_val_10b);
  RETIRE_SUCCESS
}

function clause execute (F_UN_TYPE_H(rs1, rd, FMV_X_H)) = {
  let rs1_val_H            = F(rs1)[15..0];
  let rd_val_X  : xlenbits = sign_extend(rs1_val_H);
  X(rd) = rd_val_X;
  RETIRE_SUCCESS
}

function clause execute (F_UN_TYPE_H(rs1, rd, FMV_H_X)) = {
  let rs1_val_X            = X(rs1, rs_1);
  let rd_val_H             = rs1_val_X [15..0];
  F(rd) = nan_box (rd_val_H);
  RETIRE_SUCCESS
}

/* AST -> Assembly notation ================================ */

mapping f_un_type_mnemonic_H : f_un_op_H <-> string = {
    FMV_X_H  <-> "fmv.x.h",
    FCLASS_H <-> "fclass.h",
    FMV_H_X  <-> "fmv.h.x"
}

mapping clause assembly = F_UN_TYPE_H(rs1, rd, FMV_X_H)
                      <-> f_un_type_mnemonic_H(FMV_X_H)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_name(rs1)

mapping clause assembly = F_UN_TYPE_H(rs1, rd, FMV_H_X)
                      <-> f_un_type_mnemonic_H(FMV_H_X)
                          ^ spc() ^ freg_name(rd)
                          ^ sep() ^ reg_name(rs1)

mapping clause assembly = F_UN_TYPE_H(rs1, rd, FCLASS_H)
                      <-> f_un_type_mnemonic_H(FCLASS_H)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
