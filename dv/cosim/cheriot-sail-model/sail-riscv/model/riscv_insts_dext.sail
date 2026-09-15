/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* **************************************************************** */
/* This file specifies the instructions in the D extension          */
/* (double precision floating point).                               */

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
/* Note: Rounding Modes and Floating point accrued exception flags  */
/* are defined in riscv_insts_fext.sail.                            */
/* In RISC-V, the D extension requires the F extension, so that     */
/* should have been processed before this one.                      */

/* **************************************************************** */
/* S and D value structure (sign, exponent, mantissa)               */

/* TODO: this should be a 'mapping' */
val      fsplit_D : bits(64) -> (bits(1), bits(11), bits(52))
function fsplit_D   x64 = (x64[63..63], x64[62..52], x64[51..0])

val      fmake_D  : (bits(1), bits(11), bits(52)) -> bits(64)
function fmake_D (sign, exp, mant) = sign @ exp @ mant

/* ---- Structure tests */

val      f_is_neg_inf_D : bits(64) -> bool
function f_is_neg_inf_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (sign == 0b1)
   & (exp  == ones())
   & (mant == zeros()))
}

val      f_is_neg_norm_D : bits(64) -> bool
function f_is_neg_norm_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (sign == 0b1)
   & (exp  != zeros())
   & (exp  != ones()))
}

val      f_is_neg_subnorm_D : bits(64) -> bool
function f_is_neg_subnorm_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (sign == 0b1)
   & (exp  == zeros())
   & (mant != zeros()))
}

val      f_is_neg_zero_D : bits(64) -> bool
function f_is_neg_zero_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (sign == ones())
   & (exp  == zeros())
   & (mant == zeros()))
}

val      f_is_pos_zero_D : bits(64) -> bool
function f_is_pos_zero_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (sign == zeros())
   & (exp  == zeros())
   & (mant == zeros()))
}

val      f_is_pos_subnorm_D : bits(64) -> bool
function f_is_pos_subnorm_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (sign == zeros())
   & (exp  == zeros())
   & (mant != zeros()))
}

val      f_is_pos_norm_D : bits(64) -> bool
function f_is_pos_norm_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (sign == zeros())
   & (exp  != zeros())
   & (exp  != ones()))
}

val      f_is_pos_inf_D : bits(64) -> bool
function f_is_pos_inf_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (sign == zeros())
   & (exp  == ones())
   & (mant == zeros()))
}

val      f_is_SNaN_D : bits(64) -> bool
function f_is_SNaN_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (exp == ones())
   & (mant [51] == bitzero)
   & (mant != zeros()))
}

val      f_is_QNaN_D : bits(64) -> bool
function f_is_QNaN_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (exp == ones())
   & (mant [51] == bitone))
}

/* Either QNaN or SNan */
val      f_is_NaN_D : bits(64) -> bool
function f_is_NaN_D   x64 = {
  let (sign, exp, mant) = fsplit_D (x64);
  (  (exp == ones())
   & (mant != zeros()))
}


/* **************************************************************** */
/* Help functions used in the semantic functions                    */

val      negate_D : bits(64) -> bits(64)
function negate_D (x64) = {
  let (sign, exp, mant) = fsplit_D (x64);
  let new_sign = if (sign == 0b0) then 0b1 else 0b0;
  fmake_D (new_sign, exp, mant)
}

val      feq_quiet_D : (bits(64), bits (64)) -> (bool, bits(5))
function feq_quiet_D   (v1,       v2) = {
  let (s1, e1, m1) = fsplit_D (v1);
  let (s2, e2, m2) = fsplit_D (v2);

  let v1Is0    = f_is_neg_zero_D(v1) | f_is_pos_zero_D(v1);
  let v2Is0    = f_is_neg_zero_D(v2) | f_is_pos_zero_D(v2);

  let result = ((v1 == v2) | (v1Is0 & v2Is0));

  let fflags = if   (f_is_SNaN_D(v1) | f_is_SNaN_D(v2))
               then nvFlag()
               else zeros();

  (result, fflags)
}

val      flt_D : (bits(64), bits (64), bool) -> (bool, bits(5))
function flt_D   (v1,       v2,        is_quiet) = {
  let (s1, e1, m1) = fsplit_D (v1);
  let (s2, e2, m2) = fsplit_D (v2);

  let result : bool =
    if (s1 == 0b0) & (s2 == 0b0) then
      if   (e1 == e2)
      then unsigned (m1) < unsigned (m2)
      else unsigned (e1) < unsigned (e2)
    else if (s1 == 0b0) & (s2 == 0b1) then
      false
    else if (s1 == 0b1) & (s2 == 0b0) then
      true
    else
      if   (e1 == e2)
      then unsigned (m1) > unsigned (m2)
      else unsigned (e1) > unsigned (e2);

  let fflags = if is_quiet then
                 if   (f_is_SNaN_D(v1) | f_is_SNaN_D(v2))
                 then nvFlag()
                 else zeros()
               else
                 if   (f_is_NaN_D(v1) | f_is_NaN_D(v2))
                 then nvFlag()
                 else zeros();

  (result, fflags)
}

val      fle_D : (bits(64), bits (64), bool) -> (bool, bits(5))
function fle_D   (v1,       v2,        is_quiet) = {
  let (s1, e1, m1) = fsplit_D (v1);
  let (s2, e2, m2) = fsplit_D (v2);

  let v1Is0    = f_is_neg_zero_D(v1) | f_is_pos_zero_D(v1);
  let v2Is0    = f_is_neg_zero_D(v2) | f_is_pos_zero_D(v2);

  let result : bool =
    if (s1 == 0b0) & (s2 == 0b0) then
      if   (e1 == e2)
      then unsigned (m1) <=  unsigned (m2)
      else unsigned (e1)  <  unsigned (e2)
    else if (s1 == 0b0) & (s2 == 0b1) then
      (v1Is0 & v2Is0)                         /* Equal in this case (+0=-0) */
    else if (s1 == 0b1) & (s2 == 0b0) then
      true
    else
      if   (e1 == e2)
      then unsigned (m1) >=  unsigned (m2)
      else unsigned (e1)  >  unsigned (e2);

  let fflags = if is_quiet then
                 if   (f_is_SNaN_D(v1) | f_is_SNaN_D(v2))
                 then nvFlag()
                 else zeros()
               else
                 if   (f_is_NaN_D(v1) | f_is_NaN_D(v2))
                 then nvFlag()
                 else zeros();

  (result, fflags)
}

/* **************************************************************** */
/* Helper functions for 'encdec()'                                  */

function haveDoubleFPU() -> bool = haveDExt() | haveZdinx()

/* RV32Zdinx requires even register pairs; can be omitted for code  */
/* not used for RV32Zdinx (i.e. RV64-only or D-only).               */
val validDoubleRegs : forall 'n, 'n > 0. (implicit('n), vector('n, dec, regidx)) -> bool
function validDoubleRegs(n, regs) = {
  if haveZdinx() & sizeof(xlen) == 32 then
    foreach (i from 0 to (n - 1))
      if (regs[i][0] == bitone) then return false;
  true
}

/* ****************************************************************** */
/* Floating-point loads                                               */
/* These are defined in: riscv_insts_fext.sail                        */

/* ****************************************************************** */
/* Floating-point stores                                              */
/* These are defined in: riscv_insts_fext.sail                        */

/* ****************************************************************** */
/* Fused multiply-add */

/* AST */

union clause ast = F_MADD_TYPE_D : (regidx, regidx, regidx, rounding_mode, regidx, f_madd_op_D)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_MADD_TYPE_D(rs3, rs2, rs1, rm, rd, FMADD_D)                         if haveDoubleFPU() & validDoubleRegs([rs3, rs2, rs1, rd])
<-> rs3 @ 0b01 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_0011  if haveDoubleFPU() & validDoubleRegs([rs3, rs2, rs1, rd])

mapping clause encdec =
    F_MADD_TYPE_D(rs3, rs2, rs1, rm, rd, FMSUB_D)                         if haveDoubleFPU() & validDoubleRegs([rs3, rs2, rs1, rd])
<-> rs3 @ 0b01 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_0111  if haveDoubleFPU() & validDoubleRegs([rs3, rs2, rs1, rd])

mapping clause encdec =
    F_MADD_TYPE_D(rs3, rs2, rs1, rm, rd, FNMSUB_D)                        if haveDoubleFPU() & validDoubleRegs([rs3, rs2, rs1, rd])
<-> rs3 @ 0b01 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_1011  if haveDoubleFPU() & validDoubleRegs([rs3, rs2, rs1, rd])

mapping clause encdec =
    F_MADD_TYPE_D(rs3, rs2, rs1, rm, rd, FNMADD_D)                        if haveDoubleFPU() & validDoubleRegs([rs3, rs2, rs1, rd])
<-> rs3 @ 0b01 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b100_1111  if haveDoubleFPU() & validDoubleRegs([rs3, rs2, rs1, rd])

/* Execution semantics ================================ */

function clause execute (F_MADD_TYPE_D(rs3, rs2, rs1, rm, rd, op)) = {
  let rs1_val_64b = F_or_X_D(rs1);
  let rs2_val_64b = F_or_X_D(rs2);
  let rs3_val_64b = F_or_X_D(rs3);

  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_64b) : (bits(5), bits(64)) =
        match op {
          FMADD_D  => riscv_f64MulAdd (rm_3b, rs1_val_64b, rs2_val_64b, rs3_val_64b),
          FMSUB_D  => riscv_f64MulAdd (rm_3b, rs1_val_64b, rs2_val_64b, negate_D (rs3_val_64b)),
          FNMSUB_D => riscv_f64MulAdd (rm_3b, negate_D (rs1_val_64b), rs2_val_64b, rs3_val_64b),
          FNMADD_D => riscv_f64MulAdd (rm_3b, negate_D (rs1_val_64b), rs2_val_64b, negate_D (rs3_val_64b))
        };
      accrue_fflags(fflags);
      F_or_X_D(rd) = rd_val_64b;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_madd_type_mnemonic_D : f_madd_op_D <-> string = {
    FMADD_D  <-> "fmadd.d",
    FMSUB_D  <-> "fmsub.d",
    FNMSUB_D <-> "fnmsub.d",
    FNMADD_D <-> "fnmadd.d"
}

mapping clause assembly = F_MADD_TYPE_D(rs3, rs2, rs1, rm, rd, op)
                      <-> f_madd_type_mnemonic_D(op)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)
                          ^ sep() ^ freg_or_reg_name(rs3)
                          ^ sep() ^ frm_mnemonic(rm)

/* ****************************************************************** */
/* Binary ops with rounding mode */

/* AST */

union clause ast = F_BIN_RM_TYPE_D : (regidx, regidx, rounding_mode, regidx, f_bin_rm_op_D)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_BIN_RM_TYPE_D(rs2, rs1, rm, rd, FADD_D)                             if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])
<-> 0b000_0001 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])

mapping clause encdec =
    F_BIN_RM_TYPE_D(rs2, rs1, rm, rd, FSUB_D)                             if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])
<-> 0b000_0101 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])

mapping clause encdec =
    F_BIN_RM_TYPE_D(rs2, rs1, rm, rd, FMUL_D)                             if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])
<-> 0b000_1001 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])

mapping clause encdec =
    F_BIN_RM_TYPE_D(rs2, rs1, rm, rd, FDIV_D)                             if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])
<-> 0b000_1101 @ rs2 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])

/* Execution semantics ================================ */

function clause execute (F_BIN_RM_TYPE_D(rs2, rs1, rm, rd, op)) = {
  let rs1_val_64b = F_or_X_D(rs1);
  let rs2_val_64b = F_or_X_D(rs2);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_64b) : (bits(5), bits(64)) = match op {
        FADD_D  => riscv_f64Add (rm_3b, rs1_val_64b, rs2_val_64b),
        FSUB_D  => riscv_f64Sub (rm_3b, rs1_val_64b, rs2_val_64b),
        FMUL_D  => riscv_f64Mul (rm_3b, rs1_val_64b, rs2_val_64b),
        FDIV_D  => riscv_f64Div (rm_3b, rs1_val_64b, rs2_val_64b)
      };
      accrue_fflags(fflags);
      F_or_X_D(rd) = rd_val_64b;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_bin_rm_type_mnemonic_D : f_bin_rm_op_D <-> string = {
  FADD_D  <-> "fadd.d",
  FSUB_D  <-> "fsub.d",
  FMUL_D  <-> "fmul.d",
  FDIV_D  <-> "fdiv.d"
}

mapping clause assembly = F_BIN_RM_TYPE_D(rs2, rs1, rm, rd, op)
                      <-> f_bin_rm_type_mnemonic_D(op)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)
                          ^ sep() ^ frm_mnemonic(rm)

/* ****************************************************************** */
/* Unary with rounding mode */

/* AST */

union clause ast = F_UN_RM_TYPE_D : (regidx, rounding_mode, regidx, f_un_rm_op_D)

/* AST <-> Binary encoding ================================ */

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FSQRT_D)                                      if haveDoubleFPU() & validDoubleRegs([rs1, rd])
<-> 0b010_1101 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs1, rd])

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_W_D)                                     if haveDoubleFPU() & validDoubleRegs([rs1])
<-> 0b110_0001 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs1])

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_WU_D)                                    if haveDoubleFPU() & validDoubleRegs([rs1])
<-> 0b110_0001 @ 0b00001 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs1])

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_W)                                     if haveDoubleFPU() & validDoubleRegs([rd])
<-> 0b110_1001 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rd])

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_WU)                                    if haveDoubleFPU() & validDoubleRegs([rd])
<-> 0b110_1001 @ 0b00001 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rd])

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_S_D)                                     if haveDoubleFPU() & validDoubleRegs([rs1])
<-> 0b010_0000 @ 0b00001 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs1])

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_S)                                     if haveDoubleFPU() & validDoubleRegs([rd])
<-> 0b010_0001 @ 0b00000 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rd])

/* D instructions, RV64 only */

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_L_D)                                     if haveDoubleFPU() & sizeof(xlen) >= 64
<-> 0b110_0001 @ 0b00010 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & sizeof(xlen) >= 64

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_LU_D)                                    if haveDoubleFPU() & sizeof(xlen) >= 64
<-> 0b110_0001 @ 0b00011 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & sizeof(xlen) >= 64

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_L)                                     if haveDoubleFPU() & sizeof(xlen) >= 64
<-> 0b110_1001 @ 0b00010 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & sizeof(xlen) >= 64

mapping clause encdec =
    F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_LU)                                    if haveDoubleFPU() & sizeof(xlen) >= 64
<-> 0b110_1001 @ 0b00011 @ rs1 @ encdec_rounding_mode (rm) @ rd @ 0b101_0011  if haveDoubleFPU() & sizeof(xlen) >= 64

/* Execution semantics ================================ */

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FSQRT_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_D) = riscv_f64Sqrt   (rm_3b, rs1_val_D);

      accrue_fflags(fflags);
      F_or_X_D(rd) = rd_val_D;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_W_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_W) = riscv_f64ToI32 (rm_3b, rs1_val_D);

      accrue_fflags(fflags);
      X(rd) = sign_extend (rd_val_W);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_WU_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_WU) = riscv_f64ToUi32 (rm_3b, rs1_val_D);

      accrue_fflags(fflags);
      X(rd) = sign_extend (rd_val_WU);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_W)) = {
  let rs1_val_W = X(rs1, rs_1) [31..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_D) = riscv_i32ToF64 (rm_3b, rs1_val_W);

      accrue_fflags(fflags);
      F_or_X_D(rd) = rd_val_D;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_WU)) = {
  let rs1_val_WU = X(rs1, rs_1) [31..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_D) = riscv_ui32ToF64 (rm_3b, rs1_val_WU);

      accrue_fflags(fflags);
      F_or_X_D(rd) = rd_val_D;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_S_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_S) = riscv_f64ToF32 (rm_3b, rs1_val_D);

      accrue_fflags(fflags);
      F_or_X_S(rd) = rd_val_S;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_S)) = {
  let rs1_val_S = F_or_X_S(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_D) = riscv_f32ToF64 (rm_3b, rs1_val_S);

      accrue_fflags(fflags);
      F_or_X_D(rd) = rd_val_D;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_L_D)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_D = F_or_X_D(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_L) = riscv_f64ToI64 (rm_3b, rs1_val_D);

      accrue_fflags(fflags);
      X(rd) = sign_extend(rd_val_L);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_LU_D)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_D = F_or_X_D(rs1);
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_LU) = riscv_f64ToUi64 (rm_3b, rs1_val_D);

      accrue_fflags(fflags);
      X(rd) = sign_extend(rd_val_LU);
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_L)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_L = X(rs1, rs_1)[63..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_D) = riscv_i64ToF64 (rm_3b, rs1_val_L);

      accrue_fflags(fflags);
      F_or_X_D(rd) = rd_val_D;
      RETIRE_SUCCESS
    }
  }
}

function clause execute (F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_LU)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_LU = X(rs1, rs_1)[63..0];
  match (select_instr_or_fcsr_rm (rm)) {
    None() => { handle_illegal(); RETIRE_FAIL },
    Some(rm') => {
      let rm_3b = encdec_rounding_mode(rm');
      let (fflags, rd_val_D) = riscv_ui64ToF64 (rm_3b, rs1_val_LU);

      accrue_fflags(fflags);
      F_or_X_D(rd) = rd_val_D;
      RETIRE_SUCCESS
    }
  }
}

/* AST -> Assembly notation ================================ */

mapping f_un_rm_type_mnemonic_D : f_un_rm_op_D <-> string = {
    FSQRT_D   <-> "fsqrt.d",
    FCVT_W_D  <-> "fcvt.w.d",
    FCVT_WU_D <-> "fcvt.wu.d",
    FCVT_D_W  <-> "fcvt.d.w",
    FCVT_D_WU <-> "fcvt.d.wu",

    FCVT_L_D  <-> "fcvt.l.d",
    FCVT_LU_D <-> "fcvt.lu.d",
    FCVT_D_L  <-> "fcvt.d.l",
    FCVT_D_LU <-> "fcvt.d.lu",

    FCVT_S_D  <-> "fcvt.s.d",
    FCVT_D_S  <-> "fcvt.d.s"
}

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FSQRT_D)
                      <-> f_un_rm_type_mnemonic_D(FSQRT_D)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_W_D)
                      <-> f_un_rm_type_mnemonic_D(FCVT_W_D)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_WU_D)
                      <-> f_un_rm_type_mnemonic_D(FCVT_WU_D)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_W)
                      <-> f_un_rm_type_mnemonic_D(FCVT_D_W)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_WU)
                      <-> f_un_rm_type_mnemonic_D(FCVT_D_WU)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_L_D)
                      <-> f_un_rm_type_mnemonic_D(FCVT_L_D)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_LU_D)
                      <-> f_un_rm_type_mnemonic_D(FCVT_LU_D)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_L)
                      <-> f_un_rm_type_mnemonic_D(FCVT_D_L)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_LU)
                      <-> f_un_rm_type_mnemonic_D(FCVT_D_LU)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_S_D)
                      <-> f_un_rm_type_mnemonic_D(FCVT_S_D)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

mapping clause assembly = F_UN_RM_TYPE_D(rs1, rm, rd, FCVT_D_S)
                      <-> f_un_rm_type_mnemonic_D(FCVT_D_S)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ frm_mnemonic(rm)

/* ****************************************************************** */
/* Binary, no rounding mode */

/* AST */

union clause ast = F_BIN_TYPE_D : (regidx, regidx, regidx, f_bin_op_D)

/* AST <-> Binary encoding ================================ */

mapping clause encdec = F_BIN_TYPE_D(rs2, rs1, rd, FSGNJ_D)               if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])
                    <-> 0b001_0001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])

mapping clause encdec = F_BIN_TYPE_D(rs2, rs1, rd, FSGNJN_D)              if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])
                    <-> 0b001_0001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])

mapping clause encdec = F_BIN_TYPE_D(rs2, rs1, rd, FSGNJX_D)              if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])
                    <-> 0b001_0001 @ rs2 @ rs1 @ 0b010 @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])

mapping clause encdec = F_BIN_TYPE_D(rs2, rs1, rd, FMIN_D)                if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])
                    <-> 0b001_0101 @ rs2 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])

mapping clause encdec = F_BIN_TYPE_D(rs2, rs1, rd, FMAX_D)                if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])
                    <-> 0b001_0101 @ rs2 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1, rd])

mapping clause encdec = F_BIN_TYPE_D(rs2, rs1, rd, FEQ_D)                 if haveDoubleFPU() & validDoubleRegs([rs2, rs1])
                    <-> 0b101_0001 @ rs2 @ rs1 @ 0b010 @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1])

mapping clause encdec = F_BIN_TYPE_D(rs2, rs1, rd, FLT_D)                 if haveDoubleFPU() & validDoubleRegs([rs2, rs1])
                    <-> 0b101_0001 @ rs2 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1])

mapping clause encdec = F_BIN_TYPE_D(rs2, rs1, rd, FLE_D)                 if haveDoubleFPU() & validDoubleRegs([rs2, rs1])
                    <-> 0b101_0001 @ rs2 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs2, rs1])

/* Execution semantics ================================ */

function clause execute (F_BIN_TYPE_D(rs2, rs1, rd, FSGNJ_D)) = {
  let rs1_val_D    = F_or_X_D(rs1);
  let rs2_val_D    = F_or_X_D(rs2);

  let (s1, e1, m1) = fsplit_D (rs1_val_D);
  let (s2, e2, m2) = fsplit_D (rs2_val_D);
  let rd_val_D     = fmake_D (s2, e1, m1);

  F_or_X_D(rd) = rd_val_D;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_D(rs2, rs1, rd, FSGNJN_D)) = {
  let rs1_val_D    = F_or_X_D(rs1);
  let rs2_val_D    = F_or_X_D(rs2);
  let (s1, e1, m1) = fsplit_D (rs1_val_D);
  let (s2, e2, m2) = fsplit_D (rs2_val_D);
  let rd_val_D     = fmake_D (0b1 ^ s2, e1, m1);

  F_or_X_D(rd) = rd_val_D;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_D(rs2, rs1, rd, FSGNJX_D)) = {
  let rs1_val_D    = F_or_X_D(rs1);
  let rs2_val_D    = F_or_X_D(rs2);
  let (s1, e1, m1) = fsplit_D (rs1_val_D);
  let (s2, e2, m2) = fsplit_D (rs2_val_D);
  let rd_val_D     = fmake_D (s1 ^ s2, e1, m1);

  F_or_X_D(rd) = rd_val_D;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_D(rs2, rs1, rd, FMIN_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  let rs2_val_D = F_or_X_D(rs2);

  let is_quiet  = true;
  let (rs1_lt_rs2, fflags) = fle_D (rs1_val_D, rs2_val_D, is_quiet);

  let rd_val_D  = if      (f_is_NaN_D(rs1_val_D) & f_is_NaN_D(rs2_val_D))           then canonical_NaN_D()
                  else if f_is_NaN_D(rs1_val_D)                                     then rs2_val_D
                  else if f_is_NaN_D(rs2_val_D)                                     then rs1_val_D
                  else if (f_is_neg_zero_D(rs1_val_D) & f_is_pos_zero_D(rs2_val_D)) then rs1_val_D
                  else if (f_is_neg_zero_D(rs2_val_D) & f_is_pos_zero_D(rs1_val_D)) then rs2_val_D
                  else if rs1_lt_rs2                                                then rs1_val_D
                  else /* (not rs1_lt_rs2) */                                            rs2_val_D;

  accrue_fflags(fflags);
  F_or_X_D(rd) = rd_val_D;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_D(rs2, rs1, rd, FMAX_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  let rs2_val_D = F_or_X_D(rs2);

  let is_quiet  = true;
  let (rs2_lt_rs1, fflags) = fle_D (rs2_val_D, rs1_val_D, is_quiet);

  let rd_val_D  = if      (f_is_NaN_D(rs1_val_D) & f_is_NaN_D(rs2_val_D))           then canonical_NaN_D()
                  else if f_is_NaN_D(rs1_val_D)                                     then rs2_val_D
                  else if f_is_NaN_D(rs2_val_D)                                     then rs1_val_D
                  else if (f_is_neg_zero_D(rs1_val_D) & f_is_pos_zero_D(rs2_val_D)) then rs2_val_D
                  else if (f_is_neg_zero_D(rs2_val_D) & f_is_pos_zero_D(rs1_val_D)) then rs1_val_D
                  else if rs2_lt_rs1                                                then rs1_val_D
                  else /* (not rs2_lt_rs1) */                                            rs2_val_D;

  accrue_fflags(fflags);
  F_or_X_D(rd) = rd_val_D;
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_D(rs2, rs1, rd, FEQ_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  let rs2_val_D = F_or_X_D(rs2);

  let (fflags, rd_val) : (bits_fflags, bool) =
      riscv_f64Eq (rs1_val_D, rs2_val_D);

  accrue_fflags(fflags);
  X(rd) = zero_extend(bool_to_bits(rd_val));
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_D(rs2, rs1, rd, FLT_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  let rs2_val_D = F_or_X_D(rs2);

  let (fflags, rd_val) : (bits_fflags, bool) =
      riscv_f64Lt (rs1_val_D, rs2_val_D);

  accrue_fflags(fflags);
  X(rd) = zero_extend(bool_to_bits(rd_val));
  RETIRE_SUCCESS
}

function clause execute (F_BIN_TYPE_D(rs2, rs1, rd, FLE_D)) = {
  let rs1_val_D = F_or_X_D(rs1);
  let rs2_val_D = F_or_X_D(rs2);

  let (fflags, rd_val) : (bits_fflags, bool) =
      riscv_f64Le (rs1_val_D, rs2_val_D);

  accrue_fflags(fflags);
  X(rd) = zero_extend(bool_to_bits(rd_val));
  RETIRE_SUCCESS
}

/* AST -> Assembly notation ================================ */

mapping f_bin_type_mnemonic_D : f_bin_op_D <-> string = {
    FSGNJ_D  <-> "fsgnj.d",
    FSGNJN_D <-> "fsgnjn.d",
    FSGNJX_D <-> "fsgnjx.d",
    FMIN_D   <-> "fmin.d",
    FMAX_D   <-> "fmax.d",
    FEQ_D    <-> "feq.d",
    FLT_D    <-> "flt.d",
    FLE_D    <-> "fle.d"
}

mapping clause assembly = F_BIN_TYPE_D(rs2, rs1, rd, FSGNJ_D)
                      <-> f_bin_type_mnemonic_D(FSGNJ_D)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_D(rs2, rs1, rd, FSGNJN_D)
                      <-> f_bin_type_mnemonic_D(FSGNJN_D)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_D(rs2, rs1, rd, FSGNJX_D)
                      <-> f_bin_type_mnemonic_D(FSGNJX_D)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_D(rs2, rs1, rd, FMIN_D)
                      <-> f_bin_type_mnemonic_D(FMIN_D)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_D(rs2, rs1, rd, FMAX_D)
                      <-> f_bin_type_mnemonic_D(FMAX_D)
                          ^ spc() ^ freg_or_reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_D(rs2, rs1, rd, FEQ_D)
                      <-> f_bin_type_mnemonic_D(FEQ_D)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_D(rs2, rs1, rd, FLT_D)
                      <-> f_bin_type_mnemonic_D(FLT_D)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

mapping clause assembly = F_BIN_TYPE_D(rs2, rs1, rd, FLE_D)
                      <-> f_bin_type_mnemonic_D(FLE_D)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)
                          ^ sep() ^ freg_or_reg_name(rs2)

/* ****************************************************************** */
/* Unary, no rounding mode */

union clause ast = F_UN_TYPE_D : (regidx, regidx, f_un_op_D)

/* AST <-> Binary encoding ================================ */

mapping clause encdec = F_UN_TYPE_D(rs1, rd, FCLASS_D)                        if haveDoubleFPU() & validDoubleRegs([rs1])
                    <-> 0b111_0001 @ 0b00000 @ rs1 @ 0b001 @ rd @ 0b101_0011  if haveDoubleFPU() & validDoubleRegs([rs1])

/* D instructions, RV64 only */

mapping clause encdec = F_UN_TYPE_D(rs1, rd, FMV_X_D)                         if haveDExt()
                    <-> 0b111_0001 @ 0b00000 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveDExt()

mapping clause encdec = F_UN_TYPE_D(rs1, rd, FMV_D_X)                         if haveDExt()
                    <-> 0b111_1001 @ 0b00000 @ rs1 @ 0b000 @ rd @ 0b101_0011  if haveDExt()

/* Execution semantics ================================ */

function clause execute (F_UN_TYPE_D(rs1, rd, FCLASS_D)) = {
  let rs1_val_D = F_or_X_D(rs1);

  let rd_val_10b : bits (10) =
    if      f_is_neg_inf_D     (rs1_val_D) then 0b_00_0000_0001
    else if f_is_neg_norm_D    (rs1_val_D) then 0b_00_0000_0010
    else if f_is_neg_subnorm_D (rs1_val_D) then 0b_00_0000_0100
    else if f_is_neg_zero_D    (rs1_val_D) then 0b_00_0000_1000
    else if f_is_pos_zero_D    (rs1_val_D) then 0b_00_0001_0000
    else if f_is_pos_subnorm_D (rs1_val_D) then 0b_00_0010_0000
    else if f_is_pos_norm_D    (rs1_val_D) then 0b_00_0100_0000
    else if f_is_pos_inf_D     (rs1_val_D) then 0b_00_1000_0000
    else if f_is_SNaN_D        (rs1_val_D) then 0b_01_0000_0000
    else if f_is_QNaN_D        (rs1_val_D) then 0b_10_0000_0000
    else zeros();

  X(rd) = zero_extend (rd_val_10b);
  RETIRE_SUCCESS
}

function clause execute (F_UN_TYPE_D(rs1, rd, FMV_X_D)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_D            = F(rs1)[63..0];
  let rd_val_X  : xlenbits = sign_extend(rs1_val_D);
  X(rd) = rd_val_X;
  RETIRE_SUCCESS
}

function clause execute (F_UN_TYPE_D(rs1, rd, FMV_D_X)) = {
  assert(sizeof(xlen) >= 64);
  let rs1_val_X            = X(rs1, rs_1);
  let rd_val_D             = rs1_val_X [63..0];
  F(rd) = rd_val_D;
  RETIRE_SUCCESS
}

/* AST -> Assembly notation ================================ */

mapping f_un_type_mnemonic_D : f_un_op_D <-> string = {
    FMV_X_D  <-> "fmv.x.d",
    FCLASS_D <-> "fclass.d",
    FMV_D_X  <-> "fmv.d.x"
}

mapping clause assembly = F_UN_TYPE_D(rs1, rd, FMV_X_D)
                      <-> f_un_type_mnemonic_D(FMV_X_D)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_name(rs1)

mapping clause assembly = F_UN_TYPE_D(rs1, rd, FMV_D_X)
                      <-> f_un_type_mnemonic_D(FMV_D_X)
                          ^ spc() ^ freg_name(rd)
                          ^ sep() ^ reg_name(rs1)

mapping clause assembly = F_UN_TYPE_D(rs1, rd, FCLASS_D)
                      <-> f_un_type_mnemonic_D(FCLASS_D)
                          ^ spc() ^ reg_name(rd)
                          ^ sep() ^ freg_or_reg_name(rs1)

/* ****************************************************************** */
