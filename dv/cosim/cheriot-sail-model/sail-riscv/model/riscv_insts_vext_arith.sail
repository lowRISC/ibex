/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ******************************************************************************* */
/* This file implements part of the vector extension.                              */
/* Chapter 11: Vector Integer Arithmetic Instructions                              */
/* Chapter 12: Vector Fixed-Point Arithmetic Instructions                          */
/* Chapter 16: Vector Permutation Instructions (integer part)                      */
/* ******************************************************************************* */

/* ******************************* OPIVV (VVTYPE) ******************************** */
union clause ast = VVTYPE : (vvfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_vvfunct6 : vvfunct6 <-> bits(6) = {
  VV_VADD          <-> 0b000000,
  VV_VSUB          <-> 0b000010,
  VV_VMINU         <-> 0b000100,
  VV_VMIN          <-> 0b000101,
  VV_VMAXU         <-> 0b000110,
  VV_VMAX          <-> 0b000111,
  VV_VAND          <-> 0b001001,
  VV_VOR           <-> 0b001010,
  VV_VXOR          <-> 0b001011,
  VV_VRGATHER      <-> 0b001100,
  VV_VRGATHEREI16  <-> 0b001110,
  VV_VSADDU        <-> 0b100000,
  VV_VSADD         <-> 0b100001,
  VV_VSSUBU        <-> 0b100010,
  VV_VSSUB         <-> 0b100011,
  VV_VSLL          <-> 0b100101,
  VV_VSMUL         <-> 0b100111,
  VV_VSRL          <-> 0b101000,
  VV_VSRA          <-> 0b101001,
  VV_VSSRL         <-> 0b101010,
  VV_VSSRA         <-> 0b101011
}

mapping clause encdec = VVTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_vvfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b000 @ vd @ 0b1010111 if haveVExt()

function clause execute(VVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW_pow  = get_sew_pow();
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let VLEN_pow = get_vlen_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

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
        VV_VADD          => vs2_val[i] + vs1_val[i],
        VV_VSUB          => vs2_val[i] - vs1_val[i],
        VV_VAND          => vs2_val[i] & vs1_val[i],
        VV_VOR           => vs2_val[i] | vs1_val[i],
        VV_VXOR          => vs2_val[i] ^ vs1_val[i],
        VV_VSADDU        => unsigned_saturation('m, zero_extend('m + 1, vs2_val[i]) + zero_extend('m + 1, vs1_val[i])),
        VV_VSADD         => signed_saturation('m, sign_extend('m + 1, vs2_val[i]) + sign_extend('m + 1, vs1_val[i])),
        VV_VSSUBU        => {
                              if unsigned(vs2_val[i]) < unsigned(vs1_val[i]) then zeros()
                              else unsigned_saturation('m, zero_extend('m + 1, vs2_val[i]) - zero_extend('m + 1, vs1_val[i]))
                            },
        VV_VSSUB         => signed_saturation('m, sign_extend('m + 1, vs2_val[i]) - sign_extend('m + 1, vs1_val[i])),
        VV_VSMUL         => {
                              let result_mul = to_bits('m * 2, signed(vs2_val[i]) * signed(vs1_val[i]));
                              let rounding_incr = get_fixed_rounding_incr(result_mul, 'm - 1);
                              let result_wide = (result_mul >> ('m - 1)) + zero_extend('m * 2, rounding_incr);
                              signed_saturation('m, result_wide['m..0])
                            },
        VV_VSLL          => {
                              let shift_amount = get_shift_amount(vs1_val[i], SEW);
                              vs2_val[i] << shift_amount
                            },
        VV_VSRL          => {
                              let shift_amount = get_shift_amount(vs1_val[i], SEW);
                              vs2_val[i] >> shift_amount
                            },
        VV_VSRA          => {
                              let shift_amount = get_shift_amount(vs1_val[i], SEW);
                              let v_double : bits('m * 2) = sign_extend(vs2_val[i]);
                              slice(v_double >> shift_amount, 0, SEW)
                            },
        VV_VSSRL         => {
                              let shift_amount = get_shift_amount(vs1_val[i], SEW);
                              let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
                              (vs2_val[i] >> shift_amount) + zero_extend('m, rounding_incr)
                            },
        VV_VSSRA         => {
                              let shift_amount = get_shift_amount(vs1_val[i], SEW);
                              let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
                              let v_double : bits('m * 2) = sign_extend(vs2_val[i]);
                              slice(v_double >> shift_amount, 0, SEW) + zero_extend('m, rounding_incr)
                            },
        VV_VMINU         => to_bits(SEW, min(unsigned(vs2_val[i]), unsigned(vs1_val[i]))),
        VV_VMIN          => to_bits(SEW, min(signed(vs2_val[i]), signed(vs1_val[i]))),
        VV_VMAXU         => to_bits(SEW, max(unsigned(vs2_val[i]), unsigned(vs1_val[i]))),
        VV_VMAX          => to_bits(SEW, max(signed(vs2_val[i]), signed(vs1_val[i]))),
        VV_VRGATHER      => {
                              if (vs1 == vd | vs2 == vd) then { handle_illegal(); return RETIRE_FAIL };
                              let idx = unsigned(vs1_val[i]);
                              let VLMAX = int_power(2, LMUL_pow + VLEN_pow - SEW_pow);
                              assert(VLMAX <= 'n);
                              if idx < VLMAX then vs2_val[idx] else zeros()
                            },
        VV_VRGATHEREI16  => {
                              if (vs1 == vd | vs2 == vd) then { handle_illegal(); return RETIRE_FAIL };
                              /* vrgatherei16.vv uses SEW/LMUL for the data in vs2 but EEW=16 and EMUL = (16/SEW)*LMUL for the indices in vs1 */
                              let vs1_new : vector('n, dec, bits(16)) = read_vreg(num_elem, 16, 4 + LMUL_pow - SEW_pow, vs1);
                              let idx = unsigned(vs1_new[i]);
                              let VLMAX = int_power(2, LMUL_pow + VLEN_pow - SEW_pow);
                              assert(VLMAX <= 'n);
                              if idx < VLMAX then vs2_val[idx] else zeros()
                            }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vvtype_mnemonic : vvfunct6 <-> string = {
  VV_VADD          <-> "vadd.vv",
  VV_VSUB          <-> "vsub.vv",
  VV_VAND          <-> "vand.vv",
  VV_VOR           <-> "vor.vv",
  VV_VXOR          <-> "vxor.vv",
  VV_VRGATHER      <-> "vrgather.vv",
  VV_VRGATHEREI16  <-> "vrgatherei16.vv",
  VV_VSADDU        <-> "vsaddu.vv",
  VV_VSADD         <-> "vsadd.vv",
  VV_VSSUBU        <-> "vssubu.vv",
  VV_VSSUB         <-> "vssub.vv",
  VV_VSLL          <-> "vsll.vv",
  VV_VSMUL         <-> "vsmul.vv",
  VV_VSRL          <-> "vsrl.vv",
  VV_VSRA          <-> "vsra.vv",
  VV_VSSRL         <-> "vssrl.vv",
  VV_VSSRA         <-> "vssra.vv",
  VV_VMINU         <-> "vminu.vv",
  VV_VMIN          <-> "vmin.vv",
  VV_VMAXU         <-> "vmaxu.vv",
  VV_VMAX          <-> "vmax.vv"
}

mapping clause assembly = VVTYPE(funct6, vm, vs2, vs1, vd)
  <-> vvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ************************** OPIVV (WVTYPE Narrowing) *************************** */
/* ************** Vector Narrowing Integer Right Shift Instructions ************** */
union clause ast = NVSTYPE : (nvsfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_nvsfunct6 : nvsfunct6 <-> bits(6) = {
  NVS_VNSRL       <-> 0b101100,
  NVS_VNSRA       <-> 0b101101
}

mapping clause encdec = NVSTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_nvsfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b000 @ vd @ 0b1010111 if haveVExt()

function clause execute(NVSTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_widen, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let vs1_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  assert(SEW_widen <= 64);
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        NVS_VNSRL  => {
                        let shift_amount = get_shift_amount(vs1_val[i], SEW_widen);
                        slice(vs2_val[i] >> shift_amount, 0, SEW)
                      },
        NVS_VNSRA  => {
                        let shift_amount = get_shift_amount(vs1_val[i], SEW_widen);
                        let v_double : bits('o * 2) = sign_extend(vs2_val[i]);
                        let arith_shifted : bits('o) = slice(v_double >> shift_amount, 0, SEW_widen);
                        slice(arith_shifted, 0, SEW)
                      }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping nvstype_mnemonic : nvsfunct6 <-> string = {
  NVS_VNSRL       <-> "vnsrl.wv",
  NVS_VNSRA       <-> "vnsra.wv"
}

mapping clause assembly = NVSTYPE(funct6, vm, vs2, vs1, vd)
  <-> nvstype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ************************** OPIVV (WVTYPE Narrowing) *************************** */
/* *************** Vector Narrowing Fixed-Point Clip Instructions **************** */
union clause ast = NVTYPE : (nvfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_nvfunct6 : nvfunct6 <-> bits(6) = {
  NV_VNCLIPU     <-> 0b101110,
  NV_VNCLIP      <-> 0b101111
}

mapping clause encdec = NVTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_nvfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b000 @ vd @ 0b1010111 if haveVExt()

function clause execute(NVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_widen, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let vs1_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  assert(SEW_widen <= 64);
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      let shift_amount = get_shift_amount(vs1_val[i], SEW_widen);
      let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
      result[i] = match funct6 {
        NV_VNCLIPU => {
                        let result_wide = (vs2_val[i] >> shift_amount) + zero_extend('o, rounding_incr);
                        unsigned_saturation('m, result_wide);
                      },
        NV_VNCLIP  => {
                        let v_double : bits('m * 4) = sign_extend(vs2_val[i]);
                        let result_wide = slice(v_double >> shift_amount, 0, 'o) + zero_extend('o, rounding_incr);
                        signed_saturation('m, result_wide);
                      }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping nvtype_mnemonic : nvfunct6 <-> string = {
  NV_VNCLIPU     <-> "vnclipu.wv",
  NV_VNCLIP      <-> "vnclip.wv"
}

mapping clause assembly = NVTYPE(funct6, vm, vs2, vs1, vd)
  <-> nvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ********************** OPIVV (Integer Merge Instruction) ********************** */
union clause ast = MASKTYPEV : (regidx, regidx, regidx)

mapping clause encdec = MASKTYPEV (vs2, vs1,  vd) if haveVExt()
  <-> 0b010111 @ 0b0 @ vs2 @ vs1 @ 0b000 @ vd @ 0b1010111 if haveVExt()

function clause execute(MASKTYPEV(vs2, vs1, vd)) = {
  let start_element = get_start_element();
  let end_element   = get_end_element();
  let SEW           = get_sew();
  let LMUL_pow      = get_lmul_pow();
  let num_elem      = get_num_elem(LMUL_pow, SEW); /* max(VLMAX,VLEN/SEW)) */
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / (0 - LMUL_pow); /* VLMAX */

  if illegal_vd_masked(vd) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b0, 0b00000);
  let vs1_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
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
      result[i] = if vm_val[i] then vs1_val[i] else vs2_val[i]
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = MASKTYPEV(vs2, vs1, vd)
<-> "vmerge.vvm" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ sep() ^ "v0"

/* ********************** OPIVV (Integer Move Instruction) *********************** */
union clause ast = MOVETYPEV : (regidx, regidx)

mapping clause encdec = MOVETYPEV (vs1, vd) if haveVExt()
  <-> 0b010111 @ 0b1 @ 0b00000 @ vs1 @ 0b000 @ vd @ 0b1010111 if haveVExt()

function clause execute(MOVETYPEV(vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_vd_unmasked() then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b1, 0b00000);
  let vs1_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs1);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then result[i] = vs1_val[i]
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = MOVETYPEV(vs1, vd)
  <-> "vmv.v.v" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs1)

/* ******************************* OPIVX (VXTYPE) ******************************** */
union clause ast = VXTYPE : (vxfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_vxfunct6 : vxfunct6 <-> bits(6) = {
  VX_VADD       <-> 0b000000,
  VX_VSUB       <-> 0b000010,
  VX_VRSUB      <-> 0b000011,
  VX_VMINU      <-> 0b000100,
  VX_VMIN       <-> 0b000101,
  VX_VMAXU      <-> 0b000110,
  VX_VMAX       <-> 0b000111,
  VX_VAND       <-> 0b001001,
  VX_VOR        <-> 0b001010,
  VX_VXOR       <-> 0b001011,
  VX_VSADDU     <-> 0b100000,
  VX_VSADD      <-> 0b100001,
  VX_VSSUBU     <-> 0b100010,
  VX_VSSUB      <-> 0b100011,
  VX_VSLL       <-> 0b100101,
  VX_VSMUL      <-> 0b100111,
  VX_VSRL       <-> 0b101000,
  VX_VSRA       <-> 0b101001,
  VX_VSSRL      <-> 0b101010,
  VX_VSSRA      <-> 0b101011
}

mapping clause encdec = VXTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_vxfunct6(funct6) @ vm @ vs2 @ rs1 @ 0b100 @ vd @ 0b1010111 if haveVExt()

function clause execute(VXTYPE(funct6, vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let rs1_val : bits('m)                  = get_scalar(rs1, SEW);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        VX_VADD    => vs2_val[i] + rs1_val,
        VX_VSUB    => vs2_val[i] - rs1_val,
        VX_VRSUB   => rs1_val - vs2_val[i],
        VX_VAND    => vs2_val[i] & rs1_val,
        VX_VOR     => vs2_val[i] | rs1_val,
        VX_VXOR    => vs2_val[i] ^ rs1_val,
        VX_VSADDU  => unsigned_saturation('m, zero_extend('m + 1, vs2_val[i]) + zero_extend('m + 1, rs1_val) ),
        VX_VSADD   => signed_saturation('m, sign_extend('m + 1, vs2_val[i]) + sign_extend('m + 1, rs1_val) ),
        VX_VSSUBU  => {
                        if unsigned(vs2_val[i]) < unsigned(rs1_val) then zeros()
                        else unsigned_saturation('m, zero_extend('m + 1, vs2_val[i]) - zero_extend('m + 1, rs1_val) )
                      },
        VX_VSSUB   => signed_saturation('m, sign_extend('m + 1, vs2_val[i]) - sign_extend('m + 1, rs1_val) ),
        VX_VSMUL   => {
                        let result_mul = to_bits('m * 2, signed(vs2_val[i]) * signed(rs1_val));
                        let rounding_incr = get_fixed_rounding_incr(result_mul, 'm - 1);
                        let result_wide = (result_mul >> ('m - 1)) + zero_extend('m * 2, rounding_incr);
                        signed_saturation('m, result_wide['m..0])
                      },
        VX_VSLL    => {
                        let shift_amount = get_shift_amount(rs1_val, SEW);
                        vs2_val[i] << shift_amount
                      },
        VX_VSRL    => {
                        let shift_amount = get_shift_amount(rs1_val, SEW);
                        vs2_val[i] >> shift_amount
                      },
        VX_VSRA    => {
                        let shift_amount = get_shift_amount(rs1_val, SEW);
                        let v_double : bits('m * 2) = sign_extend(vs2_val[i]);
                        slice(v_double >> shift_amount, 0, SEW)
                      },
        VX_VSSRL   => {
                        let shift_amount = get_shift_amount(rs1_val, SEW);
                        let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
                        (vs2_val[i] >> shift_amount) + zero_extend('m, rounding_incr)
                      },
        VX_VSSRA   => {
                        let shift_amount = get_shift_amount(rs1_val, SEW);
                        let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
                        let v_double : bits('m * 2) = sign_extend(vs2_val[i]);
                        slice(v_double >> shift_amount, 0, SEW) + zero_extend('m, rounding_incr)
                      },
        VX_VMINU   => to_bits(SEW, min(unsigned(vs2_val[i]), unsigned(rs1_val))),
        VX_VMIN    => to_bits(SEW, min(signed(vs2_val[i]), signed(rs1_val))),
        VX_VMAXU   => to_bits(SEW, max(unsigned(vs2_val[i]), unsigned(rs1_val))),
        VX_VMAX    => to_bits(SEW, max(signed(vs2_val[i]), signed(rs1_val)))
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vxtype_mnemonic : vxfunct6 <-> string = {
  VX_VADD       <-> "vadd.vx",
  VX_VSUB       <-> "vsub.vx",
  VX_VRSUB      <-> "vrsub.vx",
  VX_VAND       <-> "vand.vx",
  VX_VOR        <-> "vor.vx",
  VX_VXOR       <-> "vxor.vx",
  VX_VSADDU     <-> "vsaddu.vx",
  VX_VSADD      <-> "vsadd.vx",
  VX_VSSUBU     <-> "vssubu.vx",
  VX_VSSUB      <-> "vssub.vx",
  VX_VSLL       <-> "vsll.vx",
  VX_VSMUL      <-> "vsmul.vx",
  VX_VSRL       <-> "vsrl.vx",
  VX_VSRA       <-> "vsra.vx",
  VX_VSSRL      <-> "vssrl.vx",
  VX_VSSRA      <-> "vssra.vx",
  VX_VMINU      <-> "vminu.vx",
  VX_VMIN       <-> "vmin.vx",
  VX_VMAXU      <-> "vmaxu.vx",
  VX_VMAX       <-> "vmax.vx"
}

mapping clause assembly = VXTYPE(funct6, vm, vs2, rs1, vd)
  <-> vxtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* ************************** OPIVX (WXTYPE Narrowing) *************************** */
/* ************** Vector Narrowing Integer Right Shift Instructions ************** */
union clause ast = NXSTYPE : (nxsfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_nxsfunct6 : nxsfunct6 <-> bits(6) = {
  NXS_VNSRL       <-> 0b101100,
  NXS_VNSRA       <-> 0b101101
}

mapping clause encdec = NXSTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_nxsfunct6(funct6) @ vm @ vs2 @ rs1 @ 0b100 @ vd @ 0b1010111 if haveVExt()

function clause execute(NXSTYPE(funct6, vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_widen, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let rs1_val : bits('m)                  = get_scalar(rs1, SEW);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  assert(SEW_widen <= 64);
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        NXS_VNSRL  => {
                        let shift_amount = get_shift_amount(rs1_val, SEW_widen);
                        slice(vs2_val[i] >> shift_amount, 0, SEW)
                      },
        NXS_VNSRA  => {
                        let shift_amount = get_shift_amount(rs1_val, SEW_widen);
                        let v_double : bits('o * 2) = sign_extend(vs2_val[i]);
                        let arith_shifted : bits('o) = slice(v_double >> shift_amount, 0, SEW_widen);
                        slice(arith_shifted, 0, SEW)
                      }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping nxstype_mnemonic : nxsfunct6 <-> string = {
  NXS_VNSRL       <-> "vnsrl.wx",
  NXS_VNSRA       <-> "vnsra.wx"
}

mapping clause assembly = NXSTYPE(funct6, vm, vs2, rs1, vd)
  <-> nxstype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* ************************** OPIVX (WXTYPE Narrowing) *************************** */
/* *************** Vector Narrowing Fixed-Point Clip Instructions **************** */
union clause ast = NXTYPE : (nxfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_nxfunct6 : nxfunct6 <-> bits(6) = {
  NX_VNCLIPU     <-> 0b101110,
  NX_VNCLIP      <-> 0b101111
}

mapping clause encdec = NXTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_nxfunct6(funct6) @ vm @ vs2 @ rs1 @ 0b100 @ vd @ 0b1010111 if haveVExt()

function clause execute(NXTYPE(funct6, vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_widen, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let rs1_val : bits('m)                  = get_scalar(rs1, SEW);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  assert(SEW_widen <= 64);
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      let shift_amount = get_shift_amount(rs1_val, SEW_widen);
      let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
      result[i] = match funct6 {
        NX_VNCLIPU => {
                        let result_wide = (vs2_val[i] >> shift_amount) + zero_extend('o, rounding_incr);
                        unsigned_saturation('m, result_wide)
                      },
        NX_VNCLIP  => {
                        let v_double : bits('m * 4) = sign_extend(vs2_val[i]);
                        let result_wide = slice(v_double >> shift_amount, 0, 'o) + zero_extend('o, rounding_incr);
                        signed_saturation('m, result_wide)
                      }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping nxtype_mnemonic : nxfunct6 <-> string = {
  NX_VNCLIPU     <-> "vnclipu.wx",
  NX_VNCLIP      <-> "vnclip.wx"
}

mapping clause assembly = NXTYPE(funct6, vm, vs2, rs1, vd)
  <-> nxtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* ***************** OPIVX (Vector Slide & Gather Instructions) ****************** */
/* Slide and gather instructions extend rs1/imm to XLEN intead of SEW bits */
union clause ast = VXSG : (vxsgfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_vxsgfunct6 : vxsgfunct6 <-> bits(6) = {
  VX_VSLIDEUP     <-> 0b001110,
  VX_VSLIDEDOWN   <-> 0b001111,
  VX_VRGATHER     <-> 0b001100
}

mapping clause encdec = VXSG(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_vxsgfunct6(funct6) @ vm @ vs2 @ rs1 @ 0b100 @ vd @ 0b1010111 if haveVExt()

function clause execute(VXSG(funct6, vm, vs2, rs1, vd)) = {
  let SEW_pow  = get_sew_pow();
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let VLEN_pow = get_vlen_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let rs1_val : nat                       = unsigned(X(rs1, rs_1));
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        VX_VSLIDEUP    => {
                            if (vs2 == vd) then { handle_illegal(); return RETIRE_FAIL };
                            if i >= rs1_val then vs2_val[i - rs1_val] else vd_val[i]
                          },
        VX_VSLIDEDOWN  => {
                            let VLMAX = int_power(2, LMUL_pow + VLEN_pow - SEW_pow);
                            assert(VLMAX > 0 & VLMAX <= 'n);
                            if i + rs1_val < VLMAX then vs2_val[i + rs1_val] else zeros()
                          },
        VX_VRGATHER    => {
                            if (vs2 == vd) then { handle_illegal(); return RETIRE_FAIL };
                            let VLMAX = int_power(2, LMUL_pow + VLEN_pow - SEW_pow);
                            assert(VLMAX > 0 & VLMAX <= 'n);
                            if rs1_val < VLMAX then vs2_val[rs1_val] else zeros()
                          }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vxsg_mnemonic : vxsgfunct6 <-> string = {
  VX_VSLIDEUP     <-> "vslideup.vx",
  VX_VSLIDEDOWN   <-> "vslidedown.vx",
  VX_VRGATHER     <-> "vrgather.vx"
}

mapping clause assembly = VXSG(funct6, vm, vs2, rs1, vd)
  <-> vxsg_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* ********************** OPIVX (Integer Merge Instruction) ********************** */
union clause ast = MASKTYPEX : (regidx, regidx, regidx)

mapping clause encdec = MASKTYPEX(vs2, rs1, vd) if haveVExt()
  <-> 0b010111 @ 0b0 @ vs2 @ rs1 @ 0b100 @ vd @ 0b1010111 if haveVExt()

function clause execute(MASKTYPEX(vs2, rs1, vd)) = {
  let start_element = get_start_element();
  let end_element   = get_end_element();
  let SEW           = get_sew();
  let LMUL_pow      = get_lmul_pow();
  let num_elem      = get_num_elem(LMUL_pow, SEW); /* max(VLMAX,VLEN/SEW)) */
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / (0 - LMUL_pow); /* VLMAX */

  if illegal_vd_masked(vd) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b0, 0b00000);
  let rs1_val : bits('m)                  = get_scalar(rs1, SEW);
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

mapping clause assembly = MASKTYPEX(vs2, rs1, vd)
  <-> "vmerge.vxm" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ sep() ^ "v0"

/* ********************** OPIVX (Integer Move Instruction) *********************** */
union clause ast = MOVETYPEX : (regidx, regidx)

mapping clause encdec = MOVETYPEX (rs1, vd) if haveVExt()
  <-> 0b010111 @ 0b1 @ 0b00000 @ rs1 @ 0b100 @ vd @ 0b1010111 if haveVExt()

function clause execute(MOVETYPEX(rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_vd_unmasked() then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let rs1_val : bits('m)                  = get_scalar(rs1, 'm);
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

mapping clause assembly = MOVETYPEX(rs1, vd)
  <-> "vmv.v.x" ^ spc() ^ vreg_name(vd) ^ sep() ^ reg_name(rs1)

/* ******************************* OPIVI (VITYPE) ******************************** */
union clause ast = VITYPE : (vifunct6, bits(1), regidx, bits(5), regidx)

mapping encdec_vifunct6 : vifunct6 <-> bits(6) = {
  VI_VADD       <-> 0b000000,
  VI_VRSUB      <-> 0b000011,
  VI_VAND       <-> 0b001001,
  VI_VOR        <-> 0b001010,
  VI_VXOR       <-> 0b001011,
  VI_VSADDU     <-> 0b100000,
  VI_VSADD      <-> 0b100001,
  VI_VSLL       <-> 0b100101,
  VI_VSRL       <-> 0b101000,
  VI_VSRA       <-> 0b101001,
  VI_VSSRL      <-> 0b101010,
  VI_VSSRA      <-> 0b101011
}

mapping clause encdec = VITYPE(funct6, vm, vs2, simm, vd) if haveVExt()
  <-> encdec_vifunct6(funct6) @ vm @ vs2 @ simm @ 0b011 @ vd @ 0b1010111 if haveVExt()

function clause execute(VITYPE(funct6, vm, vs2, simm, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let imm_val : bits('m)                  = sign_extend(simm);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        VI_VADD    => vs2_val[i] + imm_val,
        VI_VRSUB   => imm_val - vs2_val[i],
        VI_VAND    => vs2_val[i] & imm_val,
        VI_VOR     => vs2_val[i] | imm_val,
        VI_VXOR    => vs2_val[i] ^ imm_val,
        VI_VSADDU  => unsigned_saturation('m, zero_extend('m + 1, vs2_val[i]) + zero_extend('m + 1, imm_val) ),
        VI_VSADD   => signed_saturation('m, sign_extend('m + 1, vs2_val[i]) + sign_extend('m + 1, imm_val) ),
        VI_VSLL    => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        vs2_val[i] << shift_amount
                      },
        VI_VSRL    => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        vs2_val[i] >> shift_amount
                      },
        VI_VSRA    => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        let v_double : bits('m * 2) = sign_extend(vs2_val[i]);
                        slice(v_double >> shift_amount, 0, SEW)
                      },
        VI_VSSRL   => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
                        (vs2_val[i] >> shift_amount) + zero_extend('m, rounding_incr)
                      },
        VI_VSSRA   => {
                        let shift_amount = get_shift_amount(zero_extend('m, simm), SEW);
                        let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
                        let v_double : bits('m * 2) = sign_extend(vs2_val[i]);
                        slice(v_double >> shift_amount, 0, SEW) + zero_extend('m, rounding_incr)
                      }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vitype_mnemonic : vifunct6 <-> string = {
  VI_VADD   <-> "vadd.vi",
  VI_VRSUB  <-> "vrsub.vi",
  VI_VAND   <-> "vand.vi",
  VI_VOR    <-> "vor.vi",
  VI_VXOR   <-> "vxor.vi",
  VI_VSADDU <-> "vsaddu.vi",
  VI_VSADD  <-> "vsadd.vi",
  VI_VSLL   <-> "vsll.vi",
  VI_VSRL   <-> "vsrl.vi",
  VI_VSRA   <-> "vsra.vi",
  VI_VSSRL  <-> "vssrl.vi",
  VI_VSSRA  <-> "vssra.vi"
}

mapping clause assembly = VITYPE(funct6, vm, vs2, simm, vd)
  <-> vitype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ hex_bits_5(simm) ^ maybe_vmask(vm)

/* ************************** OPIVI (WITYPE Narrowing) *************************** */
/* ************** Vector Narrowing Integer Right Shift Instructions ************** */
union clause ast = NISTYPE : (nisfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_nisfunct6 : nisfunct6 <-> bits(6) = {
  NIS_VNSRL       <-> 0b101100,
  NIS_VNSRA       <-> 0b101101
}

mapping clause encdec = NISTYPE(funct6, vm, vs2, simm, vd) if haveVExt()
  <-> encdec_nisfunct6(funct6) @ vm @ vs2 @ simm @ 0b011 @ vd @ 0b1010111 if haveVExt()

function clause execute(NISTYPE(funct6, vm, vs2, simm, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_widen, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let imm_val : bits('m)                  = sign_extend(simm);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  assert(SEW_widen <= 64);
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        NIS_VNSRL  => {
                        let shift_amount = get_shift_amount(imm_val, SEW_widen);
                        slice(vs2_val[i] >> shift_amount, 0, SEW)
                      },
        NIS_VNSRA  => {
                        let shift_amount = get_shift_amount(imm_val, SEW_widen);
                        let v_double : bits('o * 2) = sign_extend(vs2_val[i]);
                        let arith_shifted : bits('o) = slice(v_double >> shift_amount, 0, SEW_widen);
                        slice(arith_shifted, 0, SEW)
                      }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping nistype_mnemonic : nisfunct6 <-> string = {
  NIS_VNSRL       <-> "vnsrl.wi",
  NIS_VNSRA       <-> "vnsra.wi"
}

mapping clause assembly = NISTYPE(funct6, vm, vs2, simm, vd)
  <-> nistype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ hex_bits_5(simm) ^ maybe_vmask(vm)

/* ************************** OPIVI (WITYPE Narrowing) *************************** */
/* *************** Vector Narrowing Fixed-Point Clip Instructions **************** */
union clause ast = NITYPE : (nifunct6, bits(1), regidx, regidx, regidx)

mapping encdec_nifunct6 : nifunct6 <-> bits(6) = {
  NI_VNCLIPU     <-> 0b101110,
  NI_VNCLIP      <-> 0b101111
}

mapping clause encdec = NITYPE(funct6, vm, vs2, simm, vd) if haveVExt()
  <-> encdec_nifunct6(funct6) @ vm @ vs2 @ simm @ 0b011 @ vd @ 0b1010111 if haveVExt()

function clause execute(NITYPE(funct6, vm, vs2, simm, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_widen, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let imm_val : bits('m)                  = sign_extend(simm);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  assert(SEW_widen <= 64);
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      let shift_amount = get_shift_amount(imm_val, SEW_widen);
      let rounding_incr = get_fixed_rounding_incr(vs2_val[i], shift_amount);
      result[i] = match funct6 {
        NI_VNCLIPU => {
                        let result_wide = (vs2_val[i] >> shift_amount) + zero_extend('o, rounding_incr);
                        unsigned_saturation('m, result_wide)
                      },
        NI_VNCLIP  => {
                        let v_double : bits('m * 4) = sign_extend(vs2_val[i]);
                        let result_wide = slice(v_double >> shift_amount, 0, 'o) + zero_extend('o, rounding_incr);
                        signed_saturation('m, result_wide)
                      }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping nitype_mnemonic : nifunct6 <-> string = {
  NI_VNCLIPU     <-> "vnclipu.wi",
  NI_VNCLIP      <-> "vnclip.wi"
}

mapping clause assembly = NITYPE(funct6, vm, vs2, simm, vd)
  <-> nitype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ hex_bits_5(simm) ^ maybe_vmask(vm)

/* ***************** OPIVI (Vector Slide & Gather Instructions) ****************** */
/* Slide and gather instructions extend rs1/imm to XLEN intead of SEW bits */
union clause ast = VISG : (visgfunct6, bits(1), regidx, bits(5), regidx)

mapping encdec_visgfunct6 : visgfunct6 <-> bits(6) = {
  VI_VSLIDEUP     <-> 0b001110,
  VI_VSLIDEDOWN   <-> 0b001111,
  VI_VRGATHER     <-> 0b001100
}

mapping clause encdec = VISG(funct6, vm, vs2, simm, vd) if haveVExt()
  <-> encdec_visgfunct6(funct6) @ vm @ vs2 @ simm @ 0b011 @ vd @ 0b1010111 if haveVExt()

function clause execute(VISG(funct6, vm, vs2, simm, vd)) = {
  let SEW_pow  = get_sew_pow();
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let VLEN_pow = get_vlen_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let imm_val : nat                       = unsigned(zero_extend(sizeof(xlen), simm));
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        VI_VSLIDEUP    => {
                            if (vs2 == vd) then { handle_illegal(); return RETIRE_FAIL };
                            if i >= imm_val then vs2_val[i - imm_val] else vd_val[i]
                          },
        VI_VSLIDEDOWN  => {
                            let VLMAX = int_power(2, LMUL_pow + VLEN_pow - SEW_pow);
                            assert(VLMAX > 0 & VLMAX <= 'n);
                            if i + imm_val < VLMAX then vs2_val[i + imm_val] else zeros()
                          },
        VI_VRGATHER    => {
                            if (vs2 == vd) then { handle_illegal(); return RETIRE_FAIL };
                            let VLMAX = int_power(2, LMUL_pow + VLEN_pow - SEW_pow);
                            assert(VLMAX > 0 & VLMAX <= 'n);
                            if imm_val < VLMAX then vs2_val[imm_val] else zeros()
                          }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping visg_mnemonic : visgfunct6 <-> string = {
  VI_VSLIDEUP     <-> "vslideup.vi",
  VI_VSLIDEDOWN   <-> "vslidedown.vi",
  VI_VRGATHER     <-> "vrgather.vi"
}

mapping clause assembly = VISG(funct6, vm, vs2, simm, vd)
  <-> visg_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(simm) ^ maybe_vmask(vm)

/* ********************** OPIVI (Integer Merge Instruction) ********************** */
union clause ast = MASKTYPEI : (regidx, bits(5), regidx)

mapping clause encdec = MASKTYPEI(vs2, simm, vd) if haveVExt()
  <-> 0b010111 @ 0b0 @ vs2 @ simm @ 0b011 @ vd @ 0b1010111 if haveVExt()

function clause execute(MASKTYPEI(vs2, simm, vd)) = {
  let start_element = get_start_element();
  let end_element   = get_end_element();
  let SEW           = get_sew();
  let LMUL_pow      = get_lmul_pow();
  let num_elem      = get_num_elem(LMUL_pow, SEW); /* max(VLMAX,VLEN/SEW)) */
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / (0 - LMUL_pow); /* VLMAX */

  if illegal_vd_masked(vd) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b0, 0b00000);
  let imm_val : bits('m)                  = sign_extend(simm);
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
      result[i] = if vm_val[i] then imm_val else vs2_val[i]
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = MASKTYPEI(vs2, simm, vd)
  <-> "vmerge.vim" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ hex_bits_5(simm) ^ sep() ^ "v0"

/* ********************** OPIVI (Integer Move Instruction) *********************** */
union clause ast = MOVETYPEI : (regidx, bits(5))

mapping clause encdec = MOVETYPEI (vd, simm) if haveVExt()
  <-> 0b010111 @ 0b1 @ 0b00000 @ simm @ 0b011 @ vd @ 0b1010111 if haveVExt()

function clause execute(MOVETYPEI(vd, simm)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_vd_unmasked() then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b1, 0b00000);
  let imm_val : bits('m)                  = sign_extend(simm);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then result[i] = imm_val
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = MOVETYPEI(vd, simm)
  <-> "vmv.v.i" ^ spc() ^ vreg_name(vd) ^ sep() ^ hex_bits_5(simm)

/* ********************* OPIVI (Whole Vector Register Move) ********************** */
union clause ast = VMVRTYPE : (regidx, bits(5), regidx)

mapping clause encdec = VMVRTYPE(vs2, simm, vd) if haveVExt()
  <-> 0b100111 @ 0b1 @ vs2 @ simm @ 0b011 @ vd @ 0b1010111 if haveVExt()

function clause execute(VMVRTYPE(vs2, simm, vd)) = {
  let start_element = get_start_element();
  let SEW     = get_sew();
  let imm_val = unsigned(zero_extend(sizeof(xlen), simm));
  let EMUL    = imm_val + 1;

  if not(EMUL == 1 | EMUL == 2 | EMUL == 4 | EMUL == 8) then { handle_illegal(); return RETIRE_FAIL };

  let EMUL_pow = log2(EMUL);
  let num_elem = get_num_elem(EMUL_pow, SEW);
  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b1, 0b00000);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, EMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, EMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;

  foreach (i from 0 to (num_elem - 1)) {
    result[i] = if i < start_element then vd_val[i] else vs2_val[i]
  };

  write_vreg(num_elem, SEW, EMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping simm_string : bits(5) <-> string = {
  0b00000 <-> "1",
  0b00001 <-> "2",
  0b00011 <-> "4",
  0b00111 <-> "8"
}

mapping clause assembly = VMVRTYPE(vs2, simm, vd)
  <-> "vmv" ^ simm_string(simm) ^ "r.v" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2)

/* ******************************* OPMVV (VVTYPE) ******************************** */
union clause ast = MVVTYPE : (mvvfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_mvvfunct6 : mvvfunct6 <-> bits(6) = {
  MVV_VAADDU      <-> 0b001000,
  MVV_VAADD       <-> 0b001001,
  MVV_VASUBU      <-> 0b001010,
  MVV_VASUB       <-> 0b001011,
  MVV_VMUL        <-> 0b100101,
  MVV_VMULH       <-> 0b100111,
  MVV_VMULHU      <-> 0b100100,
  MVV_VMULHSU     <-> 0b100110,
  MVV_VDIVU       <-> 0b100000,
  MVV_VDIV        <-> 0b100001,
  MVV_VREMU       <-> 0b100010,
  MVV_VREM        <-> 0b100011
}

mapping clause encdec = MVVTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_mvvfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(MVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

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
        MVV_VAADDU   => {
                          let result_add = zero_extend('m + 1, vs2_val[i]) + zero_extend('m + 1, vs1_val[i]);
                          let rounding_incr = get_fixed_rounding_incr(result_add, 1);
                          slice(result_add >> 1, 0, 'm) + zero_extend('m, rounding_incr)
                        },
        MVV_VAADD    => {
                          let result_add = sign_extend('m + 1, vs2_val[i]) + sign_extend('m + 1, vs1_val[i]);
                          let rounding_incr = get_fixed_rounding_incr(result_add, 1);
                          slice(result_add >> 1, 0, 'm) + zero_extend('m, rounding_incr)
                        },
        MVV_VASUBU   => {
                          let result_sub = zero_extend('m + 1, vs2_val[i]) - zero_extend('m + 1, vs1_val[i]);
                          let rounding_incr = get_fixed_rounding_incr(result_sub, 1);
                          slice(result_sub >> 1, 0, 'm) + zero_extend('m, rounding_incr)
                        },
        MVV_VASUB    => {
                          let result_sub = sign_extend('m + 1, vs2_val[i]) - sign_extend('m + 1, vs1_val[i]);
                          let rounding_incr = get_fixed_rounding_incr(result_sub, 1);
                          slice(result_sub >> 1, 0, 'm) + zero_extend('m, rounding_incr)
                        },
        MVV_VMUL     => get_slice_int(SEW, signed(vs2_val[i]) * signed(vs1_val[i]), 0),
        MVV_VMULH    => get_slice_int(SEW, signed(vs2_val[i]) * signed(vs1_val[i]), SEW),
        MVV_VMULHU   => get_slice_int(SEW, unsigned(vs2_val[i]) * unsigned(vs1_val[i]), SEW),
        MVV_VMULHSU  => get_slice_int(SEW, signed(vs2_val[i]) * unsigned(vs1_val[i]), SEW),
        MVV_VDIVU    => {
                          let q : int = if unsigned(vs1_val[i]) == 0 then -1 else quot_round_zero(unsigned(vs2_val[i]), unsigned(vs1_val[i]));
                          to_bits(SEW, q)
                        },
        MVV_VDIV     => {
                          let elem_max : int = 2 ^ (SEW - 1) - 1;
                          let elem_min : int = 0 - 2 ^ (SEW - 1);
                          let q : int = if signed(vs1_val[i]) == 0 then -1 else quot_round_zero(signed(vs2_val[i]), signed(vs1_val[i]));
                          /* check for signed overflow */
                          let q' : int = if q > elem_max then elem_min else q;
                          to_bits(SEW, q')
                        },
        MVV_VREMU    => {
                          let r : int = if unsigned(vs1_val[i]) == 0 then unsigned(vs2_val[i]) else rem_round_zero(unsigned(vs2_val[i]), unsigned(vs1_val[i]));
                          /* signed overflow case returns zero naturally as required due to -1 divisor */
                          to_bits(SEW, r)
                        },
        MVV_VREM     => {
                          let r : int = if signed(vs1_val[i]) == 0 then signed(vs2_val[i]) else rem_round_zero(signed(vs2_val[i]), signed(vs1_val[i]));
                          /* signed overflow case returns zero naturally as required due to -1 divisor */
                          to_bits(SEW, r)
                        }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping mvvtype_mnemonic : mvvfunct6 <-> string = {
  MVV_VAADDU   <-> "vaaddu.vv",
  MVV_VAADD    <-> "vaadd.vv",
  MVV_VASUBU   <-> "vasubu.vv",
  MVV_VASUB    <-> "vasub.vv",
  MVV_VMUL     <-> "vmul.vv",
  MVV_VMULH    <-> "vmulh.vv",
  MVV_VMULHU   <-> "vmulhu.vv",
  MVV_VMULHSU  <-> "vmulhsu.vv",
  MVV_VDIVU    <-> "vdivu.vv",
  MVV_VDIV     <-> "vdiv.vv",
  MVV_VREMU    <-> "vremu.vv",
  MVV_VREM     <-> "vrem.vv"
}

mapping clause assembly = MVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> mvvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ************************* OPMVV (VVtype Multiply-Add) ************************* */
/* Multiply-Add instructions switch the order of source operands in assembly (vs1/rs1 before vs2) */
union clause ast = MVVMATYPE : (mvvmafunct6, bits(1), regidx, regidx, regidx)

mapping encdec_mvvmafunct6 : mvvmafunct6 <-> bits(6) = {
  MVV_VMACC       <-> 0b101101,
  MVV_VNMSAC      <-> 0b101111,
  MVV_VMADD       <-> 0b101001,
  MVV_VNMSUB      <-> 0b101011
}

mapping clause encdec = MVVMATYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_mvvmafunct6(funct6) @ vm @ vs2 @ vs1 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(MVVMATYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

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
        MVV_VMACC  => get_slice_int(SEW, signed(vs1_val[i]) * signed(vs2_val[i]), 0) + vd_val[i],
        MVV_VNMSAC => vd_val[i] - get_slice_int(SEW, signed(vs1_val[i]) * signed(vs2_val[i]), 0),
        MVV_VMADD  => get_slice_int(SEW, signed(vs1_val[i]) * signed(vd_val[i]), 0) + vs2_val[i],
        MVV_VNMSUB => vs2_val[i] - get_slice_int(SEW, signed(vs1_val[i]) * signed(vd_val[i]), 0)
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping mvvmatype_mnemonic : mvvmafunct6 <-> string = {
  MVV_VMACC    <-> "vmacc.vv",
  MVV_VNMSAC   <-> "vnmsac.vv",
  MVV_VMADD    <-> "vmadd.vv",
  MVV_VNMSUB   <-> "vnmsub.vv"
}

mapping clause assembly = MVVMATYPE(funct6, vm, vs2, vs1, vd)
  <-> mvvmatype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs1) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* *************************** OPMVV (VVTYPE Widening) *************************** */
union clause ast = WVVTYPE : (wvvfunct6, bits(1), regidx, regidx, regidx)
mapping encdec_wvvfunct6 : wvvfunct6 <-> bits(6) = {
  WVV_VADD       <-> 0b110001,
  WVV_VSUB       <-> 0b110011,
  WVV_VADDU      <-> 0b110000,
  WVV_VSUBU      <-> 0b110010,
  WVV_VWMUL      <-> 0b111011,
  WVV_VWMULU     <-> 0b111000,
  WVV_VWMULSU    <-> 0b111010
}

mapping clause encdec = WVVTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_wvvfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(WVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs1, vd, LMUL_pow, LMUL_pow_widen)) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };

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
        WVV_VADD    => to_bits(SEW_widen, signed(vs2_val[i]) + signed(vs1_val[i])),
        WVV_VSUB    => to_bits(SEW_widen, signed(vs2_val[i]) - signed(vs1_val[i])),
        WVV_VADDU   => to_bits(SEW_widen, unsigned(vs2_val[i]) + unsigned(vs1_val[i])),
        WVV_VSUBU   => to_bits(SEW_widen, unsigned(vs2_val[i]) - unsigned(vs1_val[i])),
        WVV_VWMUL   => to_bits(SEW_widen, signed(vs2_val[i]) * signed(vs1_val[i])),
        WVV_VWMULU  => to_bits(SEW_widen, unsigned(vs2_val[i]) * unsigned(vs1_val[i])),
        WVV_VWMULSU => to_bits(SEW_widen, signed(vs2_val[i]) * unsigned(vs1_val[i]))
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping wvvtype_mnemonic : wvvfunct6 <-> string = {
  WVV_VADD       <-> "vwadd.vv",
  WVV_VSUB       <-> "vwsub.vv",
  WVV_VADDU      <-> "vwaddu.vv",
  WVV_VSUBU      <-> "vwsubu.vv",
  WVV_VWMUL      <-> "vwmul.vv",
  WVV_VWMULU     <-> "vwmulu.vv",
  WVV_VWMULSU    <-> "vwmulsu.vv"
}

mapping clause assembly = WVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> wvvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* *************************** OPMVV (WVTYPE Widening) *************************** */
union clause ast = WVTYPE : (wvfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_wvfunct6 : wvfunct6 <-> bits(6) = {
  WV_VADD       <-> 0b110101,
  WV_VSUB       <-> 0b110111,
  WV_VADDU      <-> 0b110100,
  WV_VSUBU      <-> 0b110110
}

mapping clause encdec = WVTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_wvfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(WVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs1, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };

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
        WV_VADD  => to_bits(SEW_widen, signed(vs2_val[i]) + signed(vs1_val[i])),
        WV_VSUB  => to_bits(SEW_widen, signed(vs2_val[i]) - signed(vs1_val[i])),
        WV_VADDU => to_bits(SEW_widen, unsigned(vs2_val[i]) + unsigned(vs1_val[i])),
        WV_VSUBU => to_bits(SEW_widen, unsigned(vs2_val[i]) - unsigned(vs1_val[i]))
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping wvtype_mnemonic : wvfunct6 <-> string = {
  WV_VADD       <-> "vwadd.wv",
  WV_VSUB       <-> "vwsub.wv",
  WV_VADDU      <-> "vwaddu.wv",
  WV_VSUBU      <-> "vwsubu.wv"
}

mapping clause assembly = WVTYPE(funct6, vm, vs2, vs1, vd)
  <-> wvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ******************** OPMVV (VVtype Widening Multiply-Add) ********************* */
/* Multiply-Add instructions switch the order of source operands in assembly (vs1/rs1 before vs2) */
union clause ast = WMVVTYPE : (wmvvfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_wmvvfunct6 : wmvvfunct6 <-> bits(6) = {
  WMVV_VWMACCU   <-> 0b111100,
  WMVV_VWMACC     <-> 0b111101,
  WMVV_VWMACCSU  <-> 0b111111
}

mapping clause encdec =  WMVVTYPE(funct6, vm, vs2, vs1, vd) if haveVExt()
  <-> encdec_wmvvfunct6(funct6) @ vm @ vs2 @ vs1 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(WMVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs1, vd, LMUL_pow, LMUL_pow_widen)) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };

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
        WMVV_VWMACC   => to_bits(SEW_widen, signed(vs1_val[i]) * signed(vs2_val[i])) + vd_val[i],
        WMVV_VWMACCU  => to_bits(SEW_widen, unsigned(vs1_val[i]) * unsigned(vs2_val[i])) + vd_val[i],
        WMVV_VWMACCSU => to_bits(SEW_widen, signed(vs1_val[i]) * unsigned(vs2_val[i]))+ vd_val[i]
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping wmvvtype_mnemonic : wmvvfunct6 <-> string = {
  WMVV_VWMACCU     <-> "vwmaccu.vv",
  WMVV_VWMACC      <-> "vwmacc.vv",
  WMVV_VWMACCSU    <-> "vwmaccsu.vv"
}

mapping clause assembly = WMVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> wmvvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs1) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ****************************** OPMVV (VXUNARY0) ******************************* */
/* ******************* Vector Integer Extension (SEW/2 source) ******************* */
union clause ast = VEXT2TYPE : (vext2funct6, bits(1), regidx, regidx)

mapping vext2_vs1 : vext2funct6 <-> bits(5) = {
  VEXT2_ZVF2  <-> 0b00110,
  VEXT2_SVF2  <-> 0b00111
}

mapping clause encdec = VEXT2TYPE(funct6, vm, vs2, vd) if haveVExt()
  <-> 0b010010 @ vm @ vs2 @ vext2_vs1(funct6) @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(VEXT2TYPE(funct6, vm, vs2, vd)) = {
  let SEW = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_half = SEW / 2;
  let LMUL_pow_half = LMUL_pow - 1;

  if  illegal_variable_width(vd, vm, SEW_half, LMUL_pow_half) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_half, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_half;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_half, LMUL_pow_half, vs2);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  assert(SEW > SEW_half);
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        VEXT2_ZVF2 => zero_extend(vs2_val[i]),
        VEXT2_SVF2 => sign_extend(vs2_val[i])
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vext2type_mnemonic : vext2funct6 <-> string = {
  VEXT2_ZVF2  <-> "vzext.vf2",
  VEXT2_SVF2  <-> "vsext.vf2"
}

mapping clause assembly = VEXT2TYPE(funct6, vm, vs2, vd)
  <-> vext2type_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ****************************** OPMVV (VXUNARY0) ******************************* */
/* ******************* Vector Integer Extension (SEW/4 source) ******************* */
union clause ast = VEXT4TYPE : (vext4funct6, bits(1), regidx, regidx)

mapping vext4_vs1 : vext4funct6 <-> bits(5) = {
  VEXT4_ZVF4  <-> 0b00100,
  VEXT4_SVF4  <-> 0b00101
}

mapping clause encdec = VEXT4TYPE(funct6, vm, vs2, vd) if haveVExt()
  <-> 0b010010 @ vm @ vs2 @ vext4_vs1(funct6) @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(VEXT4TYPE(funct6, vm, vs2, vd)) = {
  let SEW = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_quart = SEW / 4;
  let LMUL_pow_quart = LMUL_pow - 2;

  if  illegal_variable_width(vd, vm, SEW_quart, LMUL_pow_quart) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_quart, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_quart;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_quart, LMUL_pow_quart, vs2);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  assert(SEW > SEW_quart);
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        VEXT4_ZVF4 => zero_extend(vs2_val[i]),
        VEXT4_SVF4 => sign_extend(vs2_val[i])
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vext4type_mnemonic : vext4funct6 <-> string = {
  VEXT4_ZVF4  <-> "vzext.vf4",
  VEXT4_SVF4  <-> "vsext.vf4"
}

mapping clause assembly = VEXT4TYPE(funct6, vm, vs2, vd)
  <-> vext4type_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ****************************** OPMVV (VXUNARY0) ******************************* */
/* ******************* Vector Integer Extension (SEW/8 source) ******************* */
union clause ast = VEXT8TYPE : (vext8funct6, bits(1), regidx, regidx)

mapping vext8_vs1 : vext8funct6 <-> bits(5) = {
  VEXT8_ZVF8  <-> 0b00010,
  VEXT8_SVF8  <-> 0b00011
}

mapping clause encdec = VEXT8TYPE(funct6, vm, vs2, vd) if haveVExt()
  <-> 0b010010 @ vm @ vs2 @ vext8_vs1(funct6) @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(VEXT8TYPE(funct6, vm, vs2, vd)) = {
  let SEW = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_eighth = SEW / 8;
  let LMUL_pow_eighth = LMUL_pow - 3;

  if  illegal_variable_width(vd, vm, SEW_eighth, LMUL_pow_eighth) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow_eighth, LMUL_pow))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_eighth;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_eighth, LMUL_pow_eighth, vs2);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  assert(SEW > SEW_eighth);
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        VEXT8_ZVF8 => zero_extend(vs2_val[i]),
        VEXT8_SVF8 => sign_extend(vs2_val[i])
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping vext8type_mnemonic : vext8funct6 <-> string = {
  VEXT8_ZVF8  <-> "vzext.vf8",
  VEXT8_SVF8  <-> "vsext.vf8"
}

mapping clause assembly = VEXT8TYPE(funct6, vm, vs2, vd)
  <-> vext8type_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ************************ OPMVV (vmv.x.s in VWXUNARY0) ************************* */
union clause ast = VMVXS : (regidx, regidx)

mapping clause encdec = VMVXS(vs2, rd) if haveVExt()
  <-> 0b010000 @ 0b1 @ vs2 @ 0b00000 @ 0b010 @ rd @ 0b1010111 if haveVExt()

function clause execute(VMVXS(vs2, rd)) = {
  let SEW      = get_sew();
  let num_elem = get_num_elem(0, SEW);

  if illegal_vd_unmasked() then { handle_illegal(); return RETIRE_FAIL };

  assert(num_elem > 0);
  let 'n = num_elem;
  let 'm = SEW;

  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, 0, vs2);
  X(rd) = if sizeof(xlen) < SEW then slice(vs2_val[0], 0, sizeof(xlen))
          else if sizeof(xlen) > SEW then sign_extend(vs2_val[0])
          else vs2_val[0];
  vstart = zeros();

  RETIRE_SUCCESS
}

mapping clause assembly = VMVXS(vs2, rd)
  <-> "vmv.x.s" ^ spc() ^ reg_name(rd) ^ sep() ^ vreg_name(vs2)

/* ********************* OPMVV (Vector Compress Instruction) ********************* */
union clause ast = MVVCOMPRESS : (regidx, regidx, regidx)

mapping clause encdec = MVVCOMPRESS(vs2, vs1, vd) if haveVExt()
  <-> 0b010111 @ 0b1 @ vs2 @ vs1 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(MVVCOMPRESS(vs2, vs1, vd)) = {
  let start_element = get_start_element();
  let end_element = get_end_element();
  let SEW = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  /* vcompress should always be executed with a vstart of 0 */
  if start_element != 0 | vs1 == vd | vs2 == vd | illegal_vd_unmasked()
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vs1_val : vector('n, dec, bool)     = read_vmask(num_elem, 0b0, vs1);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;

  /* body elements */
  vd_idx : nat = 0;
  foreach (i from 0 to (num_elem - 1)) {
    if i <= end_element then {
      if vs1_val[i] then {
        let 'p = vd_idx;
        assert('p < 'n);
        result['p] = vs2_val[i];
        vd_idx = vd_idx + 1;
      }
    }
  };
  /* tail elements */
  if vd_idx < num_elem then {
    let tail_ag : agtype = get_vtype_vta();
    let 'p = vd_idx;
    foreach (i from 'p to (num_elem - 1)) {
      result[i] = match tail_ag {
        UNDISTURBED => vd_val[i],
        AGNOSTIC    => vd_val[i] /* TODO: configuration support */
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = MVVCOMPRESS(vs2, vs1, vd)
  <-> "vcompress.vm" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1)

/* ******************************* OPMVX (VXTYPE) ******************************** */
union clause ast = MVXTYPE : (mvxfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_mvxfunct6 : mvxfunct6 <-> bits(6) = {
  MVX_VAADDU        <-> 0b001000,
  MVX_VAADD         <-> 0b001001,
  MVX_VASUBU        <-> 0b001010,
  MVX_VASUB         <-> 0b001011,
  MVX_VSLIDE1UP     <-> 0b001110,
  MVX_VSLIDE1DOWN   <-> 0b001111,
  MVX_VMUL          <-> 0b100101,
  MVX_VMULH         <-> 0b100111,
  MVX_VMULHU        <-> 0b100100,
  MVX_VMULHSU       <-> 0b100110,
  MVX_VDIVU         <-> 0b100000,
  MVX_VDIV          <-> 0b100001,
  MVX_VREMU         <-> 0b100010,
  MVX_VREM          <-> 0b100011
}

mapping clause encdec = MVXTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_mvxfunct6(funct6) @ vm @ vs2 @ rs1 @ 0b110 @ vd @ 0b1010111 if haveVExt()

function clause execute(MVXTYPE(funct6, vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let rs1_val : bits('m)                  = get_scalar(rs1, SEW);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        MVX_VAADDU       => {
                              let result_add = zero_extend('m + 1, vs2_val[i]) + zero_extend('m + 1, rs1_val);
                              let rounding_incr = get_fixed_rounding_incr(result_add, 1);
                              slice(result_add >> 1, 0, 'm) + zero_extend('m, rounding_incr)
                            },
        MVX_VAADD        => {
                              let result_add = sign_extend('m + 1, vs2_val[i]) + sign_extend('m + 1, rs1_val);
                              let rounding_incr = get_fixed_rounding_incr(result_add, 1);
                              slice(result_add >> 1, 0, 'm) + zero_extend('m, rounding_incr)
                            },
        MVX_VASUBU       => {
                              let result_sub = zero_extend('m + 1, vs2_val[i]) - zero_extend('m + 1, rs1_val);
                              let rounding_incr = get_fixed_rounding_incr(result_sub, 1);
                              slice(result_sub >> 1, 0, 'm) + zero_extend('m, rounding_incr)
                            },
        MVX_VASUB        => {
                              let result_sub = sign_extend('m + 1, vs2_val[i]) - sign_extend('m + 1, rs1_val);
                              let rounding_incr = get_fixed_rounding_incr(result_sub, 1);
                              slice(result_sub >> 1, 0, 'm) + zero_extend('m, rounding_incr)
                            },
        MVX_VSLIDE1UP    => {
                              if (vs2 == vd) then { handle_illegal(); return RETIRE_FAIL };
                              if i == 0 then rs1_val else vs2_val[i - 1]
                            },
        MVX_VSLIDE1DOWN  => {
                              let last_elem = get_end_element();
                              assert(last_elem < num_elem);
                              if i < last_elem then vs2_val[i + 1] else rs1_val
                            },
        MVX_VMUL         => get_slice_int(SEW, signed(vs2_val[i]) * signed(rs1_val), 0),
        MVX_VMULH        => get_slice_int(SEW, signed(vs2_val[i]) * signed(rs1_val), SEW),
        MVX_VMULHU       => get_slice_int(SEW, unsigned(vs2_val[i]) * unsigned(rs1_val), SEW),
        MVX_VMULHSU      => get_slice_int(SEW, signed(vs2_val[i]) * unsigned(rs1_val), SEW),
        MVX_VDIVU        => {
                              let q : int = if unsigned(rs1_val) == 0 then -1 else quot_round_zero(unsigned(vs2_val[i]), unsigned(rs1_val));
                              to_bits(SEW, q)
                            },
        MVX_VDIV         => {
                              let elem_max : int = 2 ^ (SEW - 1) - 1;
                              let elem_min : int = 0 - 2 ^ (SEW - 1);
                              let q : int = if signed(rs1_val) == 0 then -1 else quot_round_zero(signed(vs2_val[i]), signed(rs1_val));
                              /* check for signed overflow */
                              let q' : int = if q > elem_max then elem_min else q;
                              to_bits(SEW, q')
                            },
        MVX_VREMU        => {
                              let r : int = if unsigned(rs1_val) == 0 then unsigned(vs2_val[i]) else rem_round_zero(unsigned(vs2_val[i]), unsigned (rs1_val));
                              /* signed overflow case returns zero naturally as required due to -1 divisor */
                              to_bits(SEW, r)
                            },
        MVX_VREM         => {
                              let r : int = if signed(rs1_val) == 0 then signed(vs2_val[i]) else rem_round_zero(signed(vs2_val[i]), signed(rs1_val));
                              /* signed overflow case returns zero naturally as required due to -1 divisor */
                              to_bits(SEW, r)
                            }
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping mvxtype_mnemonic : mvxfunct6 <-> string = {
  MVX_VAADDU        <-> "vaaddu.vx",
  MVX_VAADD         <-> "vaadd.vx",
  MVX_VASUBU        <-> "vasubu.vx",
  MVX_VASUB         <-> "vasub.vx",
  MVX_VSLIDE1UP     <-> "vslide1up.vx",
  MVX_VSLIDE1DOWN   <-> "vslide1down.vx",
  MVX_VMUL          <-> "vmul.vx",
  MVX_VMULH         <-> "vmulh.vx",
  MVX_VMULHU        <-> "vmulhu.vx",
  MVX_VMULHSU       <-> "vmulhsu.vx",
  MVX_VDIVU         <-> "vdivu.vx",
  MVX_VDIV          <-> "vdiv.vx",
  MVX_VREMU         <-> "vremu.vx",
  MVX_VREM          <-> "vrem.vx"
}

mapping clause assembly = MVXTYPE(funct6, vm, vs2, rs1, vd)
  <-> mvxtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* ************************* OPMVX (VXtype Multiply-Add) ************************* */
/* Multiply-Add instructions switch the order of source operands in assembly (vs1/rs1 before vs2) */
union clause ast = MVXMATYPE : (mvxmafunct6, bits(1), regidx, regidx, regidx)

mapping encdec_mvxmafunct6 : mvxmafunct6 <-> bits(6) = {
  MVX_VMACC         <-> 0b101101,
  MVX_VNMSAC        <-> 0b101111,
  MVX_VMADD         <-> 0b101001,
  MVX_VNMSUB        <-> 0b101011
}

mapping clause encdec = MVXMATYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_mvxmafunct6(funct6) @ vm @ vs2 @ rs1 @ 0b110 @ vd @ 0b1010111 if haveVExt()

function clause execute(MVXMATYPE(funct6, vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let rs1_val : bits('m)                  = get_scalar(rs1, SEW);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        MVX_VMACC  => get_slice_int(SEW, signed(rs1_val) * signed(vs2_val[i]), 0) + vd_val[i],
        MVX_VNMSAC => vd_val[i] - get_slice_int(SEW, signed(rs1_val) * signed(vs2_val[i]), 0),
        MVX_VMADD  => get_slice_int(SEW, signed(rs1_val) * signed(vd_val[i]), 0) + vs2_val[i],
        MVX_VNMSUB => vs2_val[i] - get_slice_int(SEW, signed(rs1_val) * signed(vd_val[i]), 0)
      }
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping mvxmatype_mnemonic : mvxmafunct6 <-> string = {
  MVX_VMACC         <-> "vmacc.vx",
  MVX_VNMSAC        <-> "vnmsac.vx",
  MVX_VMADD         <-> "vmadd.vx",
  MVX_VNMSUB        <-> "vnmsub.vx"
}

mapping clause assembly = MVXMATYPE(funct6, vm, vs2, rs1, vd)
  <-> mvxmatype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ reg_name(rs1) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* *************************** OPMVX (VXTYPE Widening) *************************** */
union clause ast = WVXTYPE : (wvxfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_wvxfunct6 : wvxfunct6 <-> bits(6) = {
  WVX_VADD       <-> 0b110001,
  WVX_VSUB       <-> 0b110011,
  WVX_VADDU      <-> 0b110000,
  WVX_VSUBU      <-> 0b110010,
  WVX_VWMUL      <-> 0b111011,
  WVX_VWMULU     <-> 0b111000,
  WVX_VWMULSU    <-> 0b111010
}

mapping clause encdec = WVXTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_wvxfunct6(funct6) @ vm @ vs2 @ rs1 @ 0b110 @ vd @ 0b1010111 if haveVExt()

function clause execute(WVXTYPE(funct6, vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  let rs1_val : bits('m)                  = get_scalar(rs1, SEW);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        WVX_VADD    => to_bits(SEW_widen, signed(vs2_val[i]) + signed(rs1_val)),
        WVX_VSUB    => to_bits(SEW_widen, signed(vs2_val[i]) - signed(rs1_val)),
        WVX_VADDU   => to_bits(SEW_widen, unsigned(vs2_val[i]) + unsigned(rs1_val)),
        WVX_VSUBU   => to_bits(SEW_widen, unsigned(vs2_val[i]) - unsigned(rs1_val)),
        WVX_VWMUL   => to_bits(SEW_widen, signed(vs2_val[i]) * signed(rs1_val)),
        WVX_VWMULU  => to_bits(SEW_widen, unsigned(vs2_val[i]) * unsigned(rs1_val)),
        WVX_VWMULSU => to_bits(SEW_widen, signed(vs2_val[i]) * unsigned(rs1_val))
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping wvxtype_mnemonic : wvxfunct6 <-> string = {
  WVX_VADD       <-> "vwadd.vx",
  WVX_VSUB       <-> "vwsub.vx",
  WVX_VADDU      <-> "vwaddu.vx",
  WVX_VSUBU      <-> "vwsubu.vx",
  WVX_VWMUL      <-> "vwmul.vx",
  WVX_VWMULU     <-> "vwmulu.vx",
  WVX_VWMULSU    <-> "vwmulsu.vx"
}

mapping clause assembly = WVXTYPE(funct6, vm, vs2, rs1, vd)
  <-> wvxtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* *************************** OPMVX (WXTYPE Widening) *************************** */
union clause ast = WXTYPE : (wxfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_wxfunct6 : wxfunct6 <-> bits(6) = {
  WX_VADD       <-> 0b110101,
  WX_VSUB       <-> 0b110111,
  WX_VADDU      <-> 0b110100,
  WX_VSUBU      <-> 0b110110
}

mapping clause encdec = WXTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_wxfunct6(funct6) @ vm @ vs2 @ rs1 @ 0b110 @ vd @ 0b1010111 if haveVExt()

function clause execute(WXTYPE(funct6, vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen)
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  let rs1_val : bits('m)                  = get_scalar(rs1, SEW);
  let vs2_val : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vs2);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        WX_VADD  => to_bits(SEW_widen, signed(vs2_val[i]) + signed(rs1_val)),
        WX_VSUB  => to_bits(SEW_widen, signed(vs2_val[i]) - signed(rs1_val)),
        WX_VADDU => to_bits(SEW_widen, unsigned(vs2_val[i]) + unsigned(rs1_val)),
        WX_VSUBU => to_bits(SEW_widen, unsigned(vs2_val[i]) - unsigned(rs1_val))
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping wxtype_mnemonic : wxfunct6 <-> string = {
  WX_VADD       <-> "vwadd.wx",
  WX_VSUB       <-> "vwsub.wx",
  WX_VADDU      <-> "vwaddu.wx",
  WX_VSUBU      <-> "vwsubu.wx"
}

mapping clause assembly = WXTYPE(funct6, vm, vs2, rs1, vd)
  <-> wxtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)

/* ******************** OPMVX (VXtype Widening Multiply-Add) ********************* */
/* Multiply-Add instructions switch the order of source operands in assembly (vs1/rs1 before vs2) */
union clause ast =  WMVXTYPE : (wmvxfunct6, bits(1), regidx, regidx, regidx)

mapping encdec_wmvxfunct6 : wmvxfunct6 <-> bits(6) = {
  WMVX_VWMACCU    <-> 0b111100,
  WMVX_VWMACC     <-> 0b111101,
  WMVX_VWMACCUS   <-> 0b111110,
  WMVX_VWMACCSU   <-> 0b111111
}

mapping clause encdec = WMVXTYPE(funct6, vm, vs2, rs1, vd) if haveVExt()
  <-> encdec_wmvxfunct6(funct6) @ vm @ vs2 @ rs1 @ 0b110 @ vd @ 0b1010111 if haveVExt()

function clause execute(WMVXTYPE(funct6, vm, vs2, rs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);
  let SEW_widen      = SEW * 2;
  let LMUL_pow_widen = LMUL_pow + 1;

  if  illegal_variable_width(vd, vm, SEW_widen, LMUL_pow_widen) |
      not(valid_reg_overlap(vs2, vd, LMUL_pow, LMUL_pow_widen))
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;
  let 'o = SEW_widen;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('o)) = read_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd);
  let rs1_val : bits('m)                  = get_scalar(rs1, SEW);
  let vs2_val : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vs2);
  result      : vector('n, dec, bits('o)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW_widen, LMUL_pow_widen, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        WMVX_VWMACCU  => (to_bits(SEW_widen, unsigned(rs1_val) * unsigned(vs2_val[i]) )) + vd_val[i],
        WMVX_VWMACC   => (to_bits(SEW_widen, signed(rs1_val) * signed(vs2_val[i]) )) + vd_val[i],
        WMVX_VWMACCUS => (to_bits(SEW_widen, unsigned(rs1_val) * signed(vs2_val[i]) ))+ vd_val[i],
        WMVX_VWMACCSU => (to_bits(SEW_widen, signed(rs1_val) * unsigned(vs2_val[i]) ))+ vd_val[i]
      }
    }
  };

  write_vreg(num_elem, SEW_widen, LMUL_pow_widen, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping wmvxtype_mnemonic : wmvxfunct6 <-> string = {
  WMVX_VWMACCU     <-> "vwmaccu.vx",
  WMVX_VWMACC      <-> "vwmacc.vx",
  WMVX_VWMACCUS    <-> "vwmaccus.vx",
  WMVX_VWMACCSU    <-> "vwmaccsu.vx"
}

mapping clause assembly = WMVXTYPE(funct6, vm, vs2, rs1, vd)
  <-> wmvxtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ reg_name(rs1) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ****************************** OPMVX (VRXUNARY0) ****************************** */
union clause ast = VMVSX : (regidx, regidx)

mapping clause encdec = VMVSX(rs1, vd) if haveVExt()
  <-> 0b010000 @ 0b1 @ 0b00000 @ rs1 @ 0b110 @ vd @ 0b1010111 if haveVExt()

function clause execute(VMVSX(rs1, vd)) = {
  let SEW      = get_sew();
  let num_elem = get_num_elem(0, SEW);

  if illegal_vd_unmasked() then { handle_illegal(); return RETIRE_FAIL };

  assert(num_elem > 0);
  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, 0b1, 0b00000);
  let rs1_val : bits('m)                  = get_scalar(rs1, 'm);
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

mapping clause assembly = VMVSX(rs1, vd)
  <-> "vmv.s.x" ^ spc() ^ vreg_name(vd) ^ sep() ^ reg_name(rs1)
