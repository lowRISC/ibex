/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ******************************************************************************* */
/* This file implements part of the vector extension.                              */
/* Chapter 13: Vector Floating-Point Instructions                                  */
/* Chapter 16: Vector Permutation Instructions (floating-point part)               */
/* ******************************************************************************* */

/* ******************************* OPFVV (VVTYPE) ******************************** */
union clause ast = FVVTYPE : (fvvfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fvvfunct6 : fvvfunct6 <-> bits(6) = {
  FVV_VADD       <-> 0b000000,
  FVV_VSUB       <-> 0b000010,
  FVV_VMIN       <-> 0b000100,
  FVV_VMAX       <-> 0b000110,
  FVV_VSGNJ      <-> 0b001000,
  FVV_VSGNJN     <-> 0b001001,
  FVV_VSGNJX     <-> 0b001010,
  FVV_VDIV       <-> 0b100000,
  FVV_VMUL       <-> 0b100100
}

mapping clause encdec = FVVTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_fvvfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b001 @ vd @ 0b1010111 if haveVExt()

function clause execute(FVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_fp_normal(vd, vm, SEW, rm_3b) then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW != 8);

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vs1_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        FVV_VADD     => fp_add(rm_3b, vs2_val[i], vs1_val[i]),
        FVV_VSUB     => fp_sub(rm_3b, vs2_val[i], vs1_val[i]),
        FVV_VMIN     => fp_min(vs2_val[i], vs1_val[i]),
        FVV_VMAX     => fp_max(vs2_val[i], vs1_val[i]),
        FVV_VMUL     => fp_mul(rm_3b, vs2_val[i], vs1_val[i]),
        FVV_VDIV     => fp_div(rm_3b, vs2_val[i], vs1_val[i]),
        FVV_VSGNJ    => [vs1_val[i]['m - 1]] @ vs2_val[i][('m - 2)..0],
        FVV_VSGNJN   => (0b1 ^ [vs1_val[i]['m - 1]]) @ vs2_val[i][('m - 2)..0],
        FVV_VSGNJX   => ([vs2_val[i]['m - 1]] ^ [vs1_val[i]['m - 1]]) @ vs2_val[i][('m - 2)..0]
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fvvtype_mnemonic : fvvfunct6 <-> string = {
  FVV_VADD       <-> "vfadd.vv",
  FVV_VSUB       <-> "vfsub.vv",
  FVV_VMIN       <-> "vfmin.vv",
  FVV_VMAX       <-> "vfmax.vv",
  FVV_VSGNJ      <-> "vfsgnj.vv",
  FVV_VSGNJN     <-> "vfsgnjn.vv",
  FVV_VSGNJX     <-> "vfsgnjx.vv",
  FVV_VDIV       <-> "vfdiv.vv",
  FVV_VMUL       <-> "vfmul.vv"
}

mapping clause assembly = FVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> fvvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ************************* OPFVV (VVtype Multiply-Add) ************************* */
/* Multiply-Add instructions switch the order of source operands in assembly (vs1/rs1 before vs2) */
union clause ast = FVVMATYPE : (fvvmafunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fvvmafunct6 : fvvmafunct6 <-> bits(6) = {
  FVV_VMADD      <-> 0b101000,
  FVV_VNMADD     <-> 0b101001,
  FVV_VMSUB      <-> 0b101010,
  FVV_VNMSUB     <-> 0b101011,
  FVV_VMACC      <-> 0b101100,
  FVV_VNMACC     <-> 0b101101,
  FVV_VMSAC      <-> 0b101110,
  FVV_VNMSAC     <-> 0b101111
}

mapping clause encdec = FVVMATYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_fvvmafunct6(funct6) @ vm @ vs2 @ vs1 @ 0b001 @ vd @ 0b1010111 if haveVExt()

function clause execute(FVVMATYPE(funct6, vm, vs2, vs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_fp_normal(vd, vm, SEW, rm_3b) then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW != 8);

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vs1_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        FVV_VMACC    => fp_muladd(rm_3b, vs1_val[i], vs2_val[i], vd_val[i]),
        FVV_VNMACC   => fp_nmulsub(rm_3b, vs1_val[i], vs2_val[i], vd_val[i]),
        FVV_VMSAC    => fp_mulsub(rm_3b, vs1_val[i], vs2_val[i], vd_val[i]),
        FVV_VNMSAC   => fp_nmuladd(rm_3b, vs1_val[i], vs2_val[i], vd_val[i]),
        FVV_VMADD    => fp_muladd(rm_3b, vs1_val[i], vd_val[i], vs2_val[i]),
        FVV_VNMADD   => fp_nmulsub(rm_3b, vs1_val[i], vd_val[i], vs2_val[i]),
        FVV_VMSUB    => fp_mulsub(rm_3b, vs1_val[i], vd_val[i], vs2_val[i]),
        FVV_VNMSUB   => fp_nmuladd(rm_3b, vs1_val[i], vd_val[i], vs2_val[i])
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fvvmatype_mnemonic : fvvmafunct6 <-> string = {
  FVV_VMADD      <-> "vfmadd.vv",
  FVV_VNMADD     <-> "vfnmadd.vv",
  FVV_VMSUB      <-> "vfmsub.vv",
  FVV_VNMSUB     <-> "vfnmsub.vv",
  FVV_VMACC      <-> "vfmacc.vv",
  FVV_VNMACC     <-> "vfnmacc.vv",
  FVV_VMSAC      <-> "vfmsac.vv",
  FVV_VNMSAC     <-> "vfnmsac.vv"
}

mapping clause assembly = FVVMATYPE(funct6, vm, vs2, vs1, vd)
  <-> fvvmatype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs1) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* *************************** OPFVV (VVTYPE Widening) *************************** */
union clause ast = FWVVTYPE : (fwvvfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fwvvfunct6 : fwvvfunct6 <-> bits(6) = {
  FWVV_VADD       <-> 0b110000,
  FWVV_VSUB       <-> 0b110010,
  FWVV_VMUL       <-> 0b111000
}

mapping clause encdec = FWVVTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_fwvvfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b001 @ vd @ 0b1010111 if haveVExt()

function clause execute(FWVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_fp_variable_width(vd, vm, SEW, rm_3b, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs1, vd, LMUL_pow, LMUL_pow_widen)) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW >= 16 & SEW_widen <= 64);

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  let vs1_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        FWVV_VADD    => fp_add(rm_3b, fp_widen(vs2_val[i]), fp_widen(vs1_val[i])),
        FWVV_VSUB    => fp_sub(rm_3b, fp_widen(vs2_val[i]), fp_widen(vs1_val[i])),
        FWVV_VMUL    => fp_mul(rm_3b, fp_widen(vs2_val[i]), fp_widen(vs1_val[i]))
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fwvvtype_mnemonic : fwvvfunct6 <-> string = {
  FWVV_VADD       <-> "vfwadd.vv",
  FWVV_VSUB       <-> "vfwsub.vv",
  FWVV_VMUL       <-> "vfwmul.vv"
}

mapping clause assembly = FWVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> fwvvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ******************** OPFVV (VVtype Widening Multiply-Add) ********************* */
/* Multiply-Add instructions switch the order of source operands in assembly (vs1/rs1 before vs2) */
union clause ast = FWVVMATYPE : (fwvvmafunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fwvvmafunct6 : fwvvmafunct6 <-> bits(6) = {
  FWVV_VMACC      <-> 0b111100,
  FWVV_VNMACC     <-> 0b111101,
  FWVV_VMSAC      <-> 0b111110,
  FWVV_VNMSAC     <-> 0b111111
}

mapping clause encdec = FWVVMATYPE(funct6, vm, vs1, vs2, vd) if haveVExt()
  <-> encdec_fwvvmafunct6(funct6) @ vm @ vs1 @ vs2 @ 0b001 @ vd @ 0b1010111 if haveVExt()

function clause execute(FWVVMATYPE(funct6, vm, vs1, vs2, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_fp_variable_width(vd, vm, SEW, rm_3b, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs1, vd, LMUL_pow, LMUL_pow_widen)) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW >= 16 & SEW_widen <= 64);

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  let vs1_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        FWVV_VMACC   => fp_muladd(rm_3b, fp_widen(vs1_val[i]), fp_widen(vs2_val[i]), vd_val[i]),
        FWVV_VNMACC  => fp_nmulsub(rm_3b, fp_widen(vs1_val[i]), fp_widen(vs2_val[i]), vd_val[i]),
        FWVV_VMSAC   => fp_mulsub(rm_3b, fp_widen(vs1_val[i]), fp_widen(vs2_val[i]), vd_val[i]),
        FWVV_VNMSAC  => fp_nmuladd(rm_3b, fp_widen(vs1_val[i]), fp_widen(vs2_val[i]), vd_val[i])
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fwvvmatype_mnemonic : fwvvmafunct6 <-> string = {
  FWVV_VMACC      <-> "vfwmacc.vv",
  FWVV_VNMACC     <-> "vfwnmacc.vv",
  FWVV_VMSAC      <-> "vfwmsac.vv",
  FWVV_VNMSAC     <-> "vfwnmsac.vv"
}

mapping clause assembly = FWVVMATYPE(funct6, vm, vs1, vs2, vd)
  <-> fwvvmatype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs1) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* *************************** OPFVV (WVTYPE Widening) *************************** */
union clause ast = FWVTYPE : (fwvfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fwvfunct6 : fwvfunct6 <-> bits(6) = {
  FWV_VADD       <-> 0b110100,
  FWV_VSUB       <-> 0b110110
}

mapping clause encdec = FWVTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_fwvfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b001 @ vd @ 0b1010111 if haveVExt()

function clause execute(FWVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_fp_variable_width(vd, vm, SEW, rm_3b, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs1, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW >= 16 & SEW_widen <= 64);

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  let vs1_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        FWV_VADD     => fp_add(rm_3b, vs2_val[i], fp_widen(vs1_val[i])),
        FWV_VSUB     => fp_sub(rm_3b, vs2_val[i], fp_widen(vs1_val[i]))
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fwvtype_mnemonic : fwvfunct6 <-> string = {
  FWV_VADD       <-> "vfwadd.wv",
  FWV_VSUB       <-> "vfwsub.wv"
}

mapping clause assembly = FWVTYPE(funct6, vm, vs2, vs1, vd)
  <-> fwvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ****************************** OPFVV (VFUNARY0) ******************************* */
union clause ast = VFUNARY0 : (bits(1), regidx, vfunary0, regidx)

mapping encdec_vfunary0_vs1 : vfunary0 <-> bits(5) = {
  FV_CVT_XU_F       <-> 0b00000,
  FV_CVT_X_F        <-> 0b00001,
  FV_CVT_F_XU       <-> 0b00010,
  FV_CVT_F_X        <-> 0b00011,
  FV_CVT_RTZ_XU_F   <-> 0b00110,
  FV_CVT_RTZ_X_F    <-> 0b00111
}

mapping clause encdec = VFUNARY0(vm, vs2, vfunary0, vd) if haveVExt()
  <-> 0b010010 @ vm @ vs2 @ encdec_vfunary0_vs1(vfunary0) @ 0b001 @ vd @ 0b1010111 if haveVExt()

function clause execute(VFUNARY0(vm, vs2, vfunary0, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_fp_normal(vd, vm, SEW, rm_3b) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match vfunary0 {
        FV_CVT_XU_F      => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                16 => riscv_f16ToUi16(rm_3b, vs2_val[i]),
                                32 => riscv_f32ToUi32(rm_3b, vs2_val[i]),
                                64 => riscv_f64ToUi64(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FV_CVT_X_F       => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                16 => riscv_f16ToI16(rm_3b, vs2_val[i]),
                                32 => riscv_f32ToI32(rm_3b, vs2_val[i]),
                                64 => riscv_f64ToI64(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FV_CVT_F_XU      => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                16 => riscv_ui32ToF16(rm_3b, zero_extend(vs2_val[i])),
                                32 => riscv_ui32ToF32(rm_3b, vs2_val[i]),
                                64 => riscv_ui64ToF64(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FV_CVT_F_X       => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                16 => riscv_i32ToF16(rm_3b, sign_extend(vs2_val[i])),
                                32 => riscv_i32ToF32(rm_3b, vs2_val[i]),
                                64 => riscv_i64ToF64(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FV_CVT_RTZ_XU_F  => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                16 => riscv_f16ToUi16(0b001, vs2_val[i]),
                                32 => riscv_f32ToUi32(0b001, vs2_val[i]),
                                64 => riscv_f64ToUi64(0b001, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FV_CVT_RTZ_X_F   => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                16 => riscv_f16ToI16(0b001, vs2_val[i]),
                                32 => riscv_f32ToI32(0b001, vs2_val[i]),
                                64 => riscv_f64ToI64(0b001, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vfunary0_mnemonic : vfunary0 <-> string = {
  FV_CVT_XU_F       <-> "vfcvt.xu.f.v",
  FV_CVT_X_F        <-> "vfcvt.x.f.v",
  FV_CVT_F_XU       <-> "vfcvt.f.xu.v",
  FV_CVT_F_X        <-> "vfcvt.f.x.v",
  FV_CVT_RTZ_XU_F   <-> "vfcvt.rtz.xu.f.v",
  FV_CVT_RTZ_X_F    <-> "vfcvt.rtz.x.f.v"
}

mapping clause assembly = VFUNARY0(vm, vs2, vfunary0, vd)
  <-> vfunary0_mnemonic(vfunary0) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ************************** OPFVV (VFUNARY0 Widening) ************************** */
union clause ast = VFWUNARY0 : (bits(1), regidx, vfwunary0, regidx)

mapping encdec_vfwunary0_vs1 : vfwunary0 <-> bits(5) = {
  FWV_CVT_XU_F      <-> 0b01000,
  FWV_CVT_X_F       <-> 0b01001,
  FWV_CVT_F_XU      <-> 0b01010,
  FWV_CVT_F_X       <-> 0b01011,
  FWV_CVT_F_F       <-> 0b01100,
  FWV_CVT_RTZ_XU_F  <-> 0b01110,
  FWV_CVT_RTZ_X_F   <-> 0b01111
}

mapping clause encdec = VFWUNARY0(vm, vs2, vfwunary0, vd) if haveVExt()
  <-> 0b010010 @ vm @ vs2 @ encdec_vfwunary0_vs1(vfwunary0) @ 0b001 @ vd @ 0b1010111 if haveVExt()

function clause execute(VFWUNARY0(vm, vs2, vfwunary0, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_fp_variable_width(vd, vm, SEW, rm_3b, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW >= 8 & SEW_widen <= 64);

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match vfwunary0 {
        FWV_CVT_XU_F     => {
                              let (fflags, elem) : (bits_fflags, bits('o)) = match 'm {
                                8  => { handle_illegal(); return RETIRE_FAIL },
                                16 => riscv_f16ToUi32(rm_3b, vs2_val[i]),
                                32 => riscv_f32ToUi64(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FWV_CVT_X_F      => {
                              let (fflags, elem) : (bits_fflags, bits('o)) = match 'm {
                                8  => { handle_illegal(); return RETIRE_FAIL },
                                16 => riscv_f16ToI32(rm_3b, vs2_val[i]),
                                32 => riscv_f32ToI64(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FWV_CVT_F_XU     => {
                              let (fflags, elem) : (bits_fflags, bits('o)) = match 'm {
                                8  => riscv_ui32ToF16(rm_3b, zero_extend(vs2_val[i])),
                                16 => riscv_ui32ToF32(rm_3b, zero_extend(vs2_val[i])),
                                32 => riscv_ui32ToF64(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FWV_CVT_F_X      => {
                              let (fflags, elem) : (bits_fflags, bits('o)) = match 'm {
                                8  => riscv_i32ToF16(rm_3b, sign_extend(vs2_val[i])),
                                16 => riscv_i32ToF32(rm_3b, sign_extend(vs2_val[i])),
                                32 => riscv_i32ToF64(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FWV_CVT_F_F      => {
                              let (fflags, elem) : (bits_fflags, bits('o)) = match 'm {
                                8  => { handle_illegal(); return RETIRE_FAIL },
                                16 => riscv_f16ToF32(rm_3b, vs2_val[i]),
                                32 => riscv_f32ToF64(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FWV_CVT_RTZ_XU_F => {
                              let (fflags, elem) : (bits_fflags, bits('o)) = match 'm {
                                8  => { handle_illegal(); return RETIRE_FAIL },
                                16 => riscv_f16ToUi32(0b001, vs2_val[i]),
                                32 => riscv_f32ToUi64(0b001, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FWV_CVT_RTZ_X_F  => {
                              let (fflags, elem) : (bits_fflags, bits('o)) = match 'm {
                                8  => { handle_illegal(); return RETIRE_FAIL },
                                16 => riscv_f16ToI32(0b001, vs2_val[i]),
                                32 => riscv_f32ToI64(0b001, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            }
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vfwunary0_mnemonic : vfwunary0 <-> string = {
  FWV_CVT_XU_F      <-> "vfwcvt.xu.f.v",
  FWV_CVT_X_F       <-> "vfwcvt.x.f.v",
  FWV_CVT_F_XU      <-> "vfwcvt.f.xu.v",
  FWV_CVT_F_X       <-> "vfwcvt.f.x.v",
  FWV_CVT_F_F       <-> "vfwcvt.f.f.v",
  FWV_CVT_RTZ_XU_F  <-> "vfwcvt.rtz.xu.f.v",
  FWV_CVT_RTZ_X_F   <-> "vfwcvt.rtz.x.f.v"
}

mapping clause assembly = VFWUNARY0(vm, vs2, vfwunary0, vd)
  <-> vfwunary0_mnemonic(vfwunary0) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ************************* OPFVV (VFUNARY0 Narrowing) ************************** */
union clause ast = VFNUNARY0 : (bits(1), regidx, vfnunary0, regidx)

mapping encdec_vfnunary0_vs1 : vfnunary0 <-> bits(5) = {
  FNV_CVT_XU_F      <-> 0b10000,
  FNV_CVT_X_F       <-> 0b10001,
  FNV_CVT_F_XU      <-> 0b10010,
  FNV_CVT_F_X       <-> 0b10011,
  FNV_CVT_F_F       <-> 0b10100,
  FNV_CVT_ROD_F_F   <-> 0b10101,
  FNV_CVT_RTZ_XU_F  <-> 0b10110,
  FNV_CVT_RTZ_X_F   <-> 0b10111
}

mapping clause encdec = VFNUNARY0(vm, vs2, vfnunary0, vd) if haveVExt()
  <-> 0b010010 @ vm @ vs2 @ encdec_vfnunary0_vs1(vfnunary0) @ 0b001 @ vd @ 0b1010111 if haveVExt()

function clause execute(VFNUNARY0(vm, vs2, vfnunary0, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_fp_variable_width(vd, vm, SEW, rm_3b, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_widen, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match vfnunary0 {
        FNV_CVT_XU_F     => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                8  => riscv_f16ToUi8(rm_3b, vs2_val[i]),
                                16 => riscv_f32ToUi16(rm_3b, vs2_val[i]),
                                32 => riscv_f64ToUi32(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FNV_CVT_X_F      => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                8  => riscv_f16ToI8(rm_3b, vs2_val[i]),
                                16 => riscv_f32ToI16(rm_3b, vs2_val[i]),
                                32 => riscv_f64ToI32(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FNV_CVT_F_XU     => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                8  => { handle_illegal(); return RETIRE_FAIL },
                                16 => riscv_ui32ToF16(rm_3b, vs2_val[i]),
                                32 => riscv_ui64ToF32(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FNV_CVT_F_X      => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                8  => { handle_illegal(); return RETIRE_FAIL },
                                16 => riscv_i32ToF16(rm_3b, vs2_val[i]),
                                32 => riscv_i64ToF32(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FNV_CVT_F_F      => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                8  => { handle_illegal(); return RETIRE_FAIL },
                                16 => riscv_f32ToF16(rm_3b, vs2_val[i]),
                                32 => riscv_f64ToF32(rm_3b, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FNV_CVT_ROD_F_F  => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                8  => { handle_illegal(); return RETIRE_FAIL },
                                16 => riscv_f32ToF16(0b110, vs2_val[i]),
                                32 => riscv_f64ToF32(0b110, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FNV_CVT_RTZ_XU_F => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                8  => riscv_f16ToUi8(0b001, vs2_val[i]),
                                16 => riscv_f32ToUi16(0b001, vs2_val[i]),
                                32 => riscv_f64ToUi32(0b001, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            },
        FNV_CVT_RTZ_X_F  => {
                              let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                                8  => riscv_f16ToI8(0b001, vs2_val[i]),
                                16 => riscv_f32ToI16(0b001, vs2_val[i]),
                                32 => riscv_f64ToI32(0b001, vs2_val[i])
                              };
                              accrue_fflags(fflags);
                              elem
                            }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vfnunary0_mnemonic : vfnunary0 <-> string = {
  FNV_CVT_XU_F      <-> "vfncvt.xu.f.w",
  FNV_CVT_X_F       <-> "vfncvt.x.f.w",
  FNV_CVT_F_XU      <-> "vfncvt.f.xu.w",
  FNV_CVT_F_X       <-> "vfncvt.f.x.w",
  FNV_CVT_F_F       <-> "vfncvt.f.f.w",
  FNV_CVT_ROD_F_F   <-> "vfncvt.rod.f.f.w",
  FNV_CVT_RTZ_XU_F  <-> "vfncvt.rtz.xu.f.w",
  FNV_CVT_RTZ_X_F   <-> "vfncvt.rtz.x.f.w"
}

mapping clause assembly = VFNUNARY0(vm, vs2, vfnunary0, vd)
  <-> vfnunary0_mnemonic(vfnunary0) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ****************************** OPFVV (VFUNARY1) ******************************* */
union clause ast = VFUNARY1 : (bits(1), regidx, vfunary1, regidx)

mapping encdec_vfunary1_vs1 : vfunary1 <-> bits(5) = {
  FVV_VSQRT       <-> 0b00000,
  FVV_VRSQRT7     <-> 0b00100,
  FVV_VREC7       <-> 0b00101,
  FVV_VCLASS      <-> 0b10000
}

mapping clause encdec = VFUNARY1(vm, vs2, vfunary1, vd) if haveVExt()
  <-> 0b010011 @ vm @ vs2 @ encdec_vfunary1_vs1(vfunary1) @ 0b001 @ vd @ 0b1010111 if haveVExt()

function clause execute(VFUNARY1(vm, vs2, vfunary1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_fp_normal(vd, vm, SEW, rm_3b) then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW != 8);

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match vfunary1 {
        FVV_VSQRT      => {
                            let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                              16  => riscv_f16Sqrt(rm_3b, vs2_val[i]),
                              32  => riscv_f32Sqrt(rm_3b, vs2_val[i]),
                              64  => riscv_f64Sqrt(rm_3b, vs2_val[i])
                            };
                            accrue_fflags(fflags);
                            elem
                          },
        FVV_VRSQRT7    => {
                            let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                              16  => riscv_f16Rsqrte7(rm_3b, vs2_val[i]),
                              32  => riscv_f32Rsqrte7(rm_3b, vs2_val[i]),
                              64  => riscv_f64Rsqrte7(rm_3b, vs2_val[i])
                            };
                            accrue_fflags(fflags);
                            elem
                          },
        FVV_VREC7      => {
                            let (fflags, elem) : (bits_fflags, bits('m)) = match 'm {
                              16  => riscv_f16Recip7(rm_3b, vs2_val[i]),
                              32  => riscv_f32Recip7(rm_3b, vs2_val[i]),
                              64  => riscv_f64Recip7(rm_3b, vs2_val[i])
                            };
                            accrue_fflags(fflags);
                            elem
                          },
        FVV_VCLASS     => fp_class(vs2_val[i])
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vfunary1_mnemonic : vfunary1 <-> string = {
  FVV_VSQRT       <-> "vfsqrt.v",
  FVV_VRSQRT7     <-> "vfrsqrt7.v",
  FVV_VREC7       <-> "vfrec7.v",
  FVV_VCLASS      <-> "vfclass.v"
}

mapping clause assembly = VFUNARY1(vm, vs2, vfunary1, vd)
  <-> vfunary1_mnemonic(vfunary1) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ****************************** OPFVV (VWFUNARY0) ****************************** */
union clause ast = VFMVFS : (regidx, regidx)

mapping clause encdec = VFMVFS(vs2, rd) if haveVExt()
  <-> 0b010000 @ 0b1 @ vs2 @ 0b00000 @ 0b001 @ rd @ 0b1010111 if haveVExt()

function clause execute(VFMVFS(vs2, rd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let num_elem = get_num_elem(0, SEW);

  if illegal_fp_vd_unmasked(SEW, rm_3b) | SEW > sizeof(flen)
  then { handle_illegal(); return RETIRE_FAIL };
  assert(num_elem > 0 & SEW != 8);

  let 'n = num_elem;
  let 'm = SEW;

  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, 0, vs2);
  match 'm {
    16 => F_H(rd) = vs2_val[0],
    32 => F_S(rd) = vs2_val[0],
    64 => F_D(rd) = vs2_val[0]
  };
  vstart = zeros();

  RETIRE_SUCCESS
}

mapping clause assembly = VFMVFS(vs2, rd)
  <-> "vfmv.f.s" ^ spc() ^ freg_name(rd) ^ sep() ^ vreg_name(vs2)

/* ******************************* OPFVF (VFtype) ******************************** */
union clause ast = FVFTYPE : (fvffunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fvffunct6 : fvffunct6 <-> bits(6) = {
  VF_VADD          <-> 0b000000,
  VF_VSUB          <-> 0b000010,
  VF_VMIN          <-> 0b000100,
  VF_VMAX          <-> 0b000110,
  VF_VSGNJ         <-> 0b001000,
  VF_VSGNJN        <-> 0b001001,
  VF_VSGNJX        <-> 0b001010,
  VF_VSLIDE1UP     <-> 0b001110,
  VF_VSLIDE1DOWN   <-> 0b001111,
  VF_VDIV          <-> 0b100000,
  VF_VRDIV         <-> 0b100001,
  VF_VMUL          <-> 0b100100,
  VF_VRSUB         <-> 0b100111
}

mapping clause encdec = FVFTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_fvffunct6(funct6) @ vm @ vs2 @ rs1 @ 0b101 @ vd @ 0b1010111 if haveVExt()

function clause execute(FVFTYPE(funct6, vm, vs2, rs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_fp_normal(vd, vm, SEW, rm_3b) then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW != 8);

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let rs1_val : bits('m)                  = get_scalar_fp(rs1, 'm);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        VF_VADD          => fp_add(rm_3b, vs2_val[i], rs1_val),
        VF_VSUB          => fp_sub(rm_3b, vs2_val[i], rs1_val),
        VF_VRSUB         => fp_sub(rm_3b, rs1_val, vs2_val[i]),
        VF_VMIN          => fp_min(vs2_val[i], rs1_val),
        VF_VMAX          => fp_max(vs2_val[i], rs1_val),
        VF_VMUL          => fp_mul(rm_3b, vs2_val[i], rs1_val),
        VF_VDIV          => fp_div(rm_3b, vs2_val[i], rs1_val),
        VF_VRDIV         => fp_div(rm_3b, rs1_val, vs2_val[i]),
        VF_VSGNJ         => [rs1_val['m - 1]] @ vs2_val[i][('m - 2)..0],
        VF_VSGNJN        => (0b1 ^ [rs1_val['m - 1]]) @ vs2_val[i][('m - 2)..0],
        VF_VSGNJX        => ([vs2_val[i]['m - 1]] ^ [rs1_val['m - 1]]) @ vs2_val[i][('m - 2)..0],
        VF_VSLIDE1UP     => {
                              if vs2 == vd then { handle_illegal(); return RETIRE_FAIL };
                              if i == 0 then rs1_val else vs2_val[i - 1]
                            },
        VF_VSLIDE1DOWN   => {
                              let last_elem = get_end_element();
                              assert(last_elem < num_elem);
                              if i < last_elem then vs2_val[i + 1] else rs1_val
                            }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fvftype_mnemonic : fvffunct6 <-> string = {
  VF_VADD          <-> "vfadd.vf",
  VF_VSUB          <-> "vfsub.vf",
  VF_VMIN          <-> "vfmin.vf",
  VF_VMAX          <-> "vfmax.vf",
  VF_VSGNJ         <-> "vfsgnj.vf",
  VF_VSGNJN        <-> "vfsgnjn.vf",
  VF_VSGNJX        <-> "vfsgnjx.vf",
  VF_VSLIDE1UP     <-> "vfslide1up.vf",
  VF_VSLIDE1DOWN   <-> "vfslide1down.vf",
  VF_VDIV          <-> "vfdiv.vf",
  VF_VRDIV         <-> "vfrdiv.vf",
  VF_VMUL          <-> "vfmul.vf",
  VF_VRSUB         <-> "vfrsub.vf"
}

mapping clause assembly = FVFTYPE(funct6, vm, vs2, rs1, vd)
  <-> fvftype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* ************************* OPFVF (VFtype Multiply-Add) ************************* */
/* Multiply-Add instructions switch the order of source operands in assembly (vs1/rs1 before vs2) */
union clause ast = FVFMATYPE : (fvfmafunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fvfmafunct6 : fvfmafunct6 <-> bits(6) = {
  VF_VMADD      <-> 0b101000,
  VF_VNMADD     <-> 0b101001,
  VF_VMSUB      <-> 0b101010,
  VF_VNMSUB     <-> 0b101011,
  VF_VMACC      <-> 0b101100,
  VF_VNMACC     <-> 0b101101,
  VF_VMSAC      <-> 0b101110,
  VF_VNMSAC     <-> 0b101111
}

mapping clause encdec = FVFMATYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_fvfmafunct6(funct6) @ vm @ vs2 @ rs1 @ 0b101 @ vd @ 0b1010111 if haveVExt()

function clause execute(FVFMATYPE(funct6, vm, vs2, rs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_fp_normal(vd, vm, SEW, rm_3b) then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW != 8);

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let rs1_val : bits('m)                  = get_scalar_fp(rs1, 'm);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        VF_VMACC    => fp_muladd(rm_3b, rs1_val, vs2_val[i], vd_val[i]),
        VF_VNMACC   => fp_nmulsub(rm_3b, rs1_val, vs2_val[i], vd_val[i]),
        VF_VMSAC    => fp_mulsub(rm_3b, rs1_val, vs2_val[i], vd_val[i]),
        VF_VNMSAC   => fp_nmuladd(rm_3b, rs1_val, vs2_val[i], vd_val[i]),
        VF_VMADD    => fp_muladd(rm_3b, rs1_val, vd_val[i], vs2_val[i]),
        VF_VNMADD   => fp_nmulsub(rm_3b, rs1_val, vd_val[i], vs2_val[i]),
        VF_VMSUB    => fp_mulsub(rm_3b, rs1_val, vd_val[i], vs2_val[i]),
        VF_VNMSUB   => fp_nmuladd(rm_3b, rs1_val, vd_val[i], vs2_val[i])
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fvfmatype_mnemonic : fvfmafunct6 <-> string = {
  VF_VMADD      <-> "vfmadd.vf",
  VF_VNMADD     <-> "vfnmadd.vf",
  VF_VMSUB      <-> "vfmsub.vf",
  VF_VNMSUB     <-> "vfnmsub.vf",
  VF_VMACC      <-> "vfmacc.vf",
  VF_VNMACC     <-> "vfnmacc.vf",
  VF_VMSAC      <-> "vfmsac.vf",
  VF_VNMSAC     <-> "vfnmsac.vf"
}

mapping clause assembly = FVFMATYPE(funct6, vm, vs2, rs1, vd)
  <-> fvfmatype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ reg_name(rs1) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* *************************** OPFVF (VFTYPE Widening) *************************** */
union clause ast = FWVFTYPE : (fwvffunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fwvffunct6 : fwvffunct6 <-> bits(6) = {
  FWVF_VADD       <-> 0b110000,
  FWVF_VSUB       <-> 0b110010,
  FWVF_VMUL       <-> 0b111000
}

mapping clause encdec = FWVFTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_fwvffunct6(funct6) @ vm @ vs2 @ rs1 @ 0b101 @ vd @ 0b1010111 if haveVExt()

function clause execute(FWVFTYPE(funct6, vm, vs2, rs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_fp_variable_width(vd, vm, SEW, rm_3b, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW >= 16 & SEW_widen <= 64);

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  let rs1_val : bits('m)                  = get_scalar_fp(rs1, 'm);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        FWVF_VADD    => fp_add(rm_3b, fp_widen(vs2_val[i]), fp_widen(rs1_val)),
        FWVF_VSUB    => fp_sub(rm_3b, fp_widen(vs2_val[i]), fp_widen(rs1_val)),
        FWVF_VMUL    => fp_mul(rm_3b, fp_widen(vs2_val[i]), fp_widen(rs1_val))
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fwvftype_mnemonic : fwvffunct6 <-> string = {
  FWVF_VADD       <-> "vfwadd.vf",
  FWVF_VSUB       <-> "vfwsub.vf",
  FWVF_VMUL       <-> "vfwmul.vf"
}

mapping clause assembly = FWVFTYPE(funct6, vm, vs2, rs1, vd)
  <-> fwvftype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* ******************** OPFVF (VFtype Widening Multiply-Add) ********************* */
/* Multiply-Add instructions switch the order of source operands in assembly (vs1/rs1 before vs2) */
union clause ast = FWVFMATYPE : (fwvfmafunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fwvfmafunct6 : fwvfmafunct6 <-> bits(6) = {
  FWVF_VMACC      <-> 0b111100,
  FWVF_VNMACC     <-> 0b111101,
  FWVF_VMSAC      <-> 0b111110,
  FWVF_VNMSAC     <-> 0b111111
}

mapping clause encdec = FWVFMATYPE(funct6, vm, rs1, vs2, vd) if haveVExt()
  <-> encdec_fwvfmafunct6(funct6) @ vm @ vs2 @ rs1 @ 0b101 @ vd @ 0b1010111 if haveVExt()

function clause execute(FWVFMATYPE(funct6, vm, rs1, vs2, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_fp_variable_width(vd, vm, SEW, rm_3b, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW >= 16 & SEW_widen <= 64);

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  let rs1_val : bits('m)                  = get_scalar_fp(rs1, 'm);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        FWVF_VMACC   => fp_muladd(rm_3b, fp_widen(rs1_val), fp_widen(vs2_val[i]), vd_val[i]),
        FWVF_VNMACC  => fp_nmulsub(rm_3b, fp_widen(rs1_val), fp_widen(vs2_val[i]), vd_val[i]),
        FWVF_VMSAC   => fp_mulsub(rm_3b, fp_widen(rs1_val), fp_widen(vs2_val[i]), vd_val[i]),
        FWVF_VNMSAC  => fp_nmuladd(rm_3b, fp_widen(rs1_val), fp_widen(vs2_val[i]), vd_val[i])
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fwvfmatype_mnemonic : fwvfmafunct6 <-> string = {
  FWVF_VMACC      <-> "vfwmacc.vf",
  FWVF_VNMACC     <-> "vfwnmacc.vf",
  FWVF_VMSAC      <-> "vfwmsac.vf",
  FWVF_VNMSAC     <-> "vfwnmsac.vf"
}

mapping clause assembly = FWVFMATYPE(funct6, vm, rs1, vs2, vd)
  <-> fwvfmatype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ reg_name(rs1) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* *************************** OPFVF (WFTYPE Widening) *************************** */
union clause ast = FWFTYPE : (fwffunct6, bits(1), regidx, regidx, regidx)

mapping encdec_fwffunct6 : fwffunct6 <-> bits(6) = {
  FWF_VADD       <-> 0b110100,
  FWF_VSUB       <-> 0b110110
}

mapping clause encdec = FWFTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_fwffunct6(funct6) @ vm @ vs2 @ rs1 @ 0b101 @ vd @ 0b1010111 if haveVExt()

function clause execute(FWFTYPE(funct6, vm, vs2, rs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if illegal_fp_variable_width(vd, vm, SEW, rm_3b, SEW_widen, LMUL_pow_widen)
  then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW >= 16 & SEW_widen <= 64);

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  let rs1_val : bits('m)                  = get_scalar_fp(rs1, 'm);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        FWF_VADD     => fp_add(rm_3b, vs2_val[i], fp_widen(rs1_val)),
        FWF_VSUB     => fp_sub(rm_3b, vs2_val[i], fp_widen(rs1_val))
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping fwftype_mnemonic : fwffunct6 <-> string = {
  FWF_VADD       <-> "vfwadd.wf",
  FWF_VSUB       <-> "vfwsub.wf"
}

mapping clause assembly = FWFTYPE(funct6, vm, vs2, rs1, vd)
  <-> fwftype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* ************************** OPFVF (Merge Instruction) ************************** */
/* This instruction operates on all body elements regardless of mask value */
union clause ast = VFMERGE : (regidx, regidx, regidx)

mapping clause encdec = VFMERGE(vs2, rs1, vd) if haveVExt()
  <-> 0b010111 @ 0b0 @ vs2 @ rs1 @ 0b101 @ vd @ 0b1010111 if haveVExt()

function clause execute(VFMERGE(vs2, rs1, vd)) = {
  let rm_3b         = fcsr[FRM];
  let start_element = get_start_element();
  let end_element   = get_end_element();
  let SEW           = get_sew();
  let LMUL_pow      = get_lmul_pow();
  let num_elem      = get_num_elem(LMUL_pow, SEW); /* max(VLMAX,VLEN/SEW)) */
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / (0 - LMUL_pow); /* VLMAX */

  if illegal_fp_vd_masked(vd, SEW, rm_3b) then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW != 8);

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b0, 0b00000);
  let rs1_val : bits('m)                  = get_scalar_fp(rs1, 'm);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;

  let tail_ag : agtype = get_vtype_vta();
  foreach (i from 0 to (num_elem - 1)) {
    if i < start_element then {
      result[i] = vd_val[i]
    } else if i > end_element | i >= real_num_elem then {
      result[i] = match tail_ag {
        UNDISTURBED => vd_val[i],
        AGNOSTIC    => vd_val[i] /* TODO: configuration support */
      }
    } else {
      /* the merge operates on all body elements */
      result[i] = if vm_val[i] then rs1_val else vs2_val[i]
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VFMERGE(vs2, rs1, vd)
  <-> "vfmerge.vfm" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ sep() ^ "v0"

/* ************************** OPFVF (Move Instruction) *************************** */
/* This instruction shares the encoding with vfmerge.vfm, but with vm=1 and vs2=v0 */
union clause ast = VFMV : (regidx, regidx)

mapping clause encdec = VFMV(rs1, vd) if haveVExt()
  <-> 0b010111 @ 0b1 @ 0b00000 @ rs1 @ 0b101 @ vd @ 0b1010111 if haveVExt()

function clause execute(VFMV(rs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_fp_vd_unmasked(SEW, rm_3b) then { handle_illegal(); return RETIRE_FAIL };
  assert(SEW != 8);

  let 'n = num_elem;
  let 'm = SEW;

  let rs1_val : bits('m)                  = get_scalar_fp(rs1, 'm);
  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b1, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then result[i] = rs1_val
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VFMV(rs1, vd)
  <-> "vfmv.v.f" ^ spc() ^ vreg_name(vd) ^ sep() ^ reg_name(rs1)

/* ****************************** OPFVF (VRFUNARY0) ****************************** */
union clause ast = VFMVSF : (regidx, regidx)

mapping clause encdec = VFMVSF(rs1, vd) if haveVExt()
  <-> 0b010000 @ 0b1 @ 0b00000 @ rs1 @ 0b101 @ vd @ 0b1010111 if haveVExt()

function clause execute(VFMVSF(rs1, vd)) = {
  let rm_3b    = fcsr[FRM];
  let SEW      = get_sew();
  let num_elem = get_num_elem(0, SEW);

  if illegal_fp_vd_unmasked(SEW, rm_3b) then { handle_illegal(); return RETIRE_FAIL };
  assert(num_elem > 0 & SEW != 8);

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b1, 0b00000);
  let rs1_val : bits('m)                  = get_scalar_fp(rs1, 'm);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, 0, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, 0, vd_val, vm_val);

  /* one body element */
  if mask[0] then result[0] = rs1_val;

  /* others treated as tail elements */
  let tail_ag : agtype = get_vtype_vta();
  foreach (i from 1 to (num_elem - 1)) {
    result[i] = match tail_ag {
      UNDISTURBED => vd_val[i],
      AGNOSTIC    => vd_val[i] /* TODO: configuration support */
    }
  };

  write_vreg(num_elem, SEW, 0, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VFMVSF(rs1, vd)
  <-> "vfmv.s.f" ^ spc() ^ vreg_name(vd) ^ sep() ^ freg_name(rs1)
