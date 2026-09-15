/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ******************************************************************************* */
/* This file implements part of the vector extension.                              */
/* Chapter 15: vector mask instructions                                            */
/* ******************************************************************************* */

/* ******************************* OPMVV (MMTYPE) ******************************** */
union clause ast = MMTYPE : (mmfunct6, regidx, regidx, regidx)

mapping encdec_mmfunct6 : mmfunct6 <-> bits(6) = {
  MM_VMAND     <-> 0b011001,
  MM_VMNAND    <-> 0b011101,
  MM_VMANDNOT  <-> 0b011000,
  MM_VMXOR     <-> 0b011011,
  MM_VMOR      <-> 0b011010,
  MM_VMNOR     <-> 0b011110,
  MM_VMORNOT   <-> 0b011100,
  MM_VMXNOR    <-> 0b011111
}

mapping clause encdec = MMTYPE(funct6, vs2, vs1, vd) if haveVExt()
  <-> encdec_mmfunct6(funct6) @ 0b1 @ vs2 @ vs1 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(MMTYPE(funct6, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = unsigned(vlenb) * 8;

  if illegal_vd_unmasked() then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vs1_val : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vs1);
  let vs2_val : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vs2);
  let vd_val  : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vd);
  result      : vector('n, dec, bool) = undefined;
  mask        : vector('n, dec, bool) = undefined;

  (result, mask) = init_masked_result_carry(num_elem, SEW, 0, vd_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = match funct6 {
        MM_VMAND     => vs2_val[i] & vs1_val[i],
        MM_VMNAND    => not(vs2_val[i] & vs1_val[i]),
        MM_VMANDNOT  => vs2_val[i] & not(vs1_val[i]),
        MM_VMXOR     => vs2_val[i] != vs1_val[i],
        MM_VMOR      => vs2_val[i] | vs1_val[i],
        MM_VMNOR     => not(vs2_val[i] | vs1_val[i]),
        MM_VMORNOT   => vs2_val[i] | not(vs1_val[i]),
        MM_VMXNOR    => vs2_val[i] == vs1_val[i]
      }
    }
  };

  write_vmask(num_elem, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping mmtype_mnemonic : mmfunct6 <-> string = {
  MM_VMAND     <-> "vmand.mm",
  MM_VMNAND    <-> "vmnand.mm",
  MM_VMANDNOT  <-> "vmandnot.mm",
  MM_VMXOR     <-> "vmxor.mm",
  MM_VMOR      <-> "vmor.mm",
  MM_VMNOR     <-> "vmnor.mm",
  MM_VMORNOT   <-> "vmornot.mm",
  MM_VMXNOR    <-> "vmxnor.mm"
}

mapping clause assembly = MMTYPE(funct6, vs2, vs1, vd)
  <-> mmtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1)

/* ************************* OPMVV (vpopc in VWXUNARY0) ************************** */
union clause ast = VCPOP_M : (bits(1), regidx, regidx)

mapping clause encdec = VCPOP_M(vm, vs2, rd) if haveVExt()
  <-> 0b010000 @ vm @ vs2 @ 0b10000 @ 0b010 @ rd @ 0b1010111 if haveVExt()

function clause execute(VCPOP_M(vm, vs2, rd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = unsigned(vlenb) * 8;

  if illegal_vd_unmasked() | not(assert_vstart(0)) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vs2);
  result      : vector('n, dec, bool) = undefined;
  mask        : vector('n, dec, bool) = undefined;

  (result, mask) = init_masked_result_cmp(num_elem, SEW, 0, vs2_val, vm_val);

  count : nat = 0;
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] & vs2_val[i] then count = count + 1;
  };

  X(rd) = to_bits(sizeof(xlen), count);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VCPOP_M(vm, vs2, rd)
  <-> "vpopc.m" ^ spc() ^ reg_name(rd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ************************* OPMVV (vfirst in VWXUNARY0) ************************* */
union clause ast = VFIRST_M : (bits(1), regidx, regidx)

mapping clause encdec = VFIRST_M(vm, vs2, rd) if haveVExt()
  <-> 0b010000 @ vm @ vs2 @ 0b10001 @ 0b010 @ rd @ 0b1010111 if haveVExt()

function clause execute(VFIRST_M(vm, vs2, rd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = unsigned(vlenb) * 8;

  if illegal_vd_unmasked() | not(assert_vstart(0)) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vs2);
  result      : vector('n, dec, bool) = undefined;
  mask        : vector('n, dec, bool) = undefined;

  (result, mask) = init_masked_result_cmp(num_elem, SEW, 0, vs2_val, vm_val);

  index : int = -1;
  foreach (i from 0 to (num_elem - 1)) {
    if index == -1 then {
      if mask[i] & vs2_val[i] then index = i;
    };
  };

  X(rd) = to_bits(sizeof(xlen), index);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VFIRST_M(vm, vs2, rd)
  <-> "vfirst.m" ^ spc() ^ reg_name(rd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ************************** OPMVV (vmsbf in VMUNARY0) ************************** */
union clause ast = VMSBF_M : (bits(1), regidx, regidx)

mapping clause encdec = VMSBF_M(vm, vs2, vd) if haveVExt()
  <-> 0b010100 @ vm @ vs2 @ 0b00001 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(VMSBF_M(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = unsigned(vlenb) * 8;

  if illegal_normal(vd, vm) | not(assert_vstart(0)) | vd == vs2
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vs2);
  let vd_val  : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vd);
  result      : vector('n, dec, bool) = undefined;
  mask        : vector('n, dec, bool) = undefined;

  (result, mask) = init_masked_result_cmp(num_elem, SEW, 0, vd_val, vm_val);

  found_elem : bool = false;
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      if vs2_val[i] then found_elem = true;
      result[i] = if found_elem then false else true
    }
  };

  write_vmask(num_elem, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VMSBF_M(vm, vs2, vd)
  <-> "vmsbf.m" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ************************** OPMVV (vmsif in VMUNARY0) ************************** */
union clause ast = VMSIF_M : (bits(1), regidx, regidx)

mapping clause encdec = VMSIF_M(vm, vs2, vd) if haveVExt()
  <-> 0b010100 @ vm @ vs2 @ 0b00011 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(VMSIF_M(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = unsigned(vlenb) * 8;

  if illegal_normal(vd, vm) | not(assert_vstart(0)) | vd == vs2
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vs2);
  let vd_val  : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vd);
  result      : vector('n, dec, bool) = undefined;
  mask        : vector('n, dec, bool) = undefined;

  (result, mask) = init_masked_result_cmp(num_elem, SEW, 0, vd_val, vm_val);

  found_elem : bool = false;
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = if found_elem then false else true;
      if vs2_val[i] then found_elem = true
    }
  };

  write_vmask(num_elem, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VMSIF_M(vm, vs2, vd)
  <-> "vmsif.m" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ************************** OPMVV (vmsof in VMUNARY0) ************************** */
union clause ast = VMSOF_M : (bits(1), regidx, regidx)

mapping clause encdec = VMSOF_M(vm, vs2, vd) if haveVExt()
  <-> 0b010100 @ vm @ vs2 @ 0b00010 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(VMSOF_M(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = unsigned(vlenb) * 8;

  if illegal_normal(vd, vm) | not(assert_vstart(0)) | vd == vs2
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vs2);
  let vd_val  : vector('n, dec, bool) = read_vmask(num_elem, 0b0, vd);
  result      : vector('n, dec, bool) = undefined;
  mask        : vector('n, dec, bool) = undefined;

  (result, mask) = init_masked_result_cmp(num_elem, SEW, 0, vd_val, vm_val);

  found_elem : bool = false;
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      if vs2_val[i] & not(found_elem) then {
        result[i] = true;
        found_elem = true
      } else {
        result[i] = false
      }
    }
  };

  write_vmask(num_elem, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VMSOF_M(vm, vs2, vd)
  <-> "vmsof.m" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* ************************** OPMVV (viota in VMUNARY0) ************************** */
union clause ast = VIOTA_M : (bits(1), regidx, regidx)

mapping clause encdec = VIOTA_M(vm, vs2, vd) if haveVExt()
  <-> 0b010100 @ vm @ vs2 @ 0b10000 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(VIOTA_M(vm, vs2, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) | not(assert_vstart(0)) | vd == vs2
  then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vs2_val : vector('n, dec, bool)     = read_vmask(num_elem, 0b0, vs2);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  sum : int = 0;
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then {
      result[i] = to_bits(SEW, sum);
      if vs2_val[i] then sum = sum + 1
    }
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VIOTA_M(vm, vs2, vd)
  <-> "viota.m" ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ maybe_vmask(vm)

/* *************************** OPMVV (vid in VMUNARY0) *************************** */
union clause ast = VID_V : (bits(1), regidx)

mapping clause encdec = VID_V(vm, vd) if haveVExt()
  <-> 0b010100 @ vm @ 0b00000 @ 0b10001 @ 0b010 @ vd @ 0b1010111 if haveVExt()

function clause execute(VID_V(vm, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  if illegal_normal(vd, vm) then { handle_illegal(); return RETIRE_FAIL };

  let 'n = num_elem;
  let 'm = SEW;

  let vm_val  : vector('n, dec, bool)     = read_vmask(num_elem, vm, 0b00000);
  let vd_val  : vector('n, dec, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);
  result      : vector('n, dec, bits('m)) = undefined;
  mask        : vector('n, dec, bool)     = undefined;

  (result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then result[i] = to_bits(SEW, i)
  };

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  vstart = zeros();
  RETIRE_SUCCESS
}

mapping clause assembly = VID_V(vm, vd)
  <-> "vid.v" ^ spc() ^ vreg_name(vd) ^ maybe_vmask(vm)
