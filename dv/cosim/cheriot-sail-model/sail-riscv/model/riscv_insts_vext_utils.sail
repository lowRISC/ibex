/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ******************************************************************************* */
/* This file implements functions used by vector instructions.                     */
/* ******************************************************************************* */

/* Vector mask mapping */
mapping maybe_vmask : string <-> bits(1) = {
  ""              <-> 0b1, /* unmasked by default */
  sep() ^ "v0.t"  <-> 0b0
}

/* Check for valid EEW and EMUL values in:
 *  1. vector widening/narrowing instructions
 *  2. vector load/store instructions
 */
val valid_eew_emul : (int, int) -> bool
function valid_eew_emul(EEW, EMUL_pow) = {
  let ELEN = int_power(2, get_elen_pow());
  EEW >= 8 & EEW <= ELEN & EMUL_pow >= -3 & EMUL_pow <= 3
}

/* Check for valid vtype setting
 *  1. If the vill bit is set, then any attempt to execute a vector instruction that depends upon vtype will raise an illegal instruction exception.
 *  2. vset{i}vl{i} and whole-register loads, stores, and moves do not depend upon vtype.
 */
val valid_vtype : unit -> bool
function valid_vtype() = {
  vtype[vill] == 0b0
}

/* Check for vstart value */
val assert_vstart : int -> bool
function assert_vstart(i) = {
  unsigned(vstart) == i
}

/* Check for valid floating-point operation types
 *  1. Valid element width of floating-point numbers
 *  2. Valid floating-point rounding mode
 */
val valid_fp_op : ({|8, 16, 32, 64|}, bits(3)) -> bool
function valid_fp_op(SEW, rm_3b) = {
  /* 128-bit floating-point values will be supported in future extensions */
  let valid_sew = (SEW >= 16 & SEW <= 128);
  let valid_rm = not(rm_3b == 0b101 | rm_3b == 0b110 | rm_3b == 0b111);
  valid_sew & valid_rm
}

/* Check for valid destination register when vector masking is enabled:
 *  The destination vector register group for a masked vector instruction
 *  cannot overlap the source mask register (v0),
 *  unless the destination vector register is being written with a mask value (e.g., compares)
 *  or the scalar result of a reduction.
 */
val valid_rd_mask : (regidx, bits(1)) -> bool
function valid_rd_mask(rd, vm) = {
  vm != 0b0 | rd != 0b00000
}

/* Check for valid register overlap in vector widening/narrowing instructions:
 *  In a widening instruction, the overlap is valid only in the highest-numbered part
 *  of the destination register group, and the source EMUL is at least 1.
 *  In a narrowing instruction, the overlap is valid only in the lowest-numbered part
 *  of the source register group.
 */
val valid_reg_overlap : (regidx, regidx, int, int) -> bool
function valid_reg_overlap(rs, rd, EMUL_pow_rs, EMUL_pow_rd) = {
  let rs_group = if EMUL_pow_rs > 0 then int_power(2, EMUL_pow_rs) else 1;
  let rd_group = if EMUL_pow_rd > 0 then int_power(2, EMUL_pow_rd) else 1;
  let rs_int = unsigned(rs);
  let rd_int = unsigned(rd);
  if EMUL_pow_rs < EMUL_pow_rd then {
    (rs_int + rs_group <= rd_int) | (rs_int >= rd_int + rd_group) |
    ((rs_int + rs_group == rd_int + rd_group) & (EMUL_pow_rs >= 0))
  } else if EMUL_pow_rs > EMUL_pow_rd then {
    (rd_int <= rs_int) | (rd_int >= rs_int + rs_group)
  } else true;
}

/* Check for valid register grouping in vector segment load/store instructions:
 *  The EMUL of load vd or store vs3 times the number of fields per segment
 *  must not be larger than 8. (EMUL * NFIELDS <= 8)
 */
val valid_segment : (int, int) -> bool
function valid_segment(nf, EMUL_pow) = {
  if EMUL_pow < 0 then nf / int_power(2, 0 - EMUL_pow) <= 8
  else nf * int_power(2, EMUL_pow) <= 8
}

/* ******************************************************************************* */
/* The following functions summarize patterns of illegal instruction check.        */
/* ******************************************************************************* */

/* a. Normal check including vtype.vill field and vd/v0 overlap if vm = 0 */
val illegal_normal : (regidx, bits(1)) -> bool
function illegal_normal(vd, vm) = {
  not(valid_vtype()) | not(valid_rd_mask(vd, vm))
}

/* b. Masked check for instructions encoded with vm = 0 */
val illegal_vd_masked : regidx -> bool
function illegal_vd_masked(vd) = {
  not(valid_vtype()) | vd == 0b00000
}

/* c. Unmasked check for:
 *  1. instructions encoded with vm = 1
 *  2. instructions with scalar rd: vcpop.m, vfirst.m
 *  3. vd as mask register (eew = 1):
 *     vmadc.vvm/vxm/vim, vmsbc.vvm/vxm, mask logical, integer compare, vlm.v, vsm.v
 */
val illegal_vd_unmasked : unit -> bool
function illegal_vd_unmasked() = {
  not(valid_vtype())
}

/* d. Variable width check for:
 *  1. integer/fixed-point widening/narrowing instructions
 *  2. vector integer extension: vzext, vsext
 */
val illegal_variable_width : (regidx, bits(1), int, int) -> bool
function illegal_variable_width(vd, vm, SEW_new, LMUL_pow_new) = {
  not(valid_vtype()) | not(valid_rd_mask(vd, vm)) | not(valid_eew_emul(SEW_new, LMUL_pow_new))
}

/* e. Normal check for reduction instructions:
 *  The destination vector register can overlap the source operands, including the mask register.
 *  Vector reduction operations raise an illegal instruction exception if vstart is non-zero.
 */
val illegal_reduction : unit -> bool
function illegal_reduction() = {
  not(valid_vtype()) | not(assert_vstart(0))
}

/* f. Variable width check for widening reduction instructions */
val illegal_reduction_widen : (int, int) -> bool
function illegal_reduction_widen(SEW_widen, LMUL_pow_widen) = {
  not(valid_vtype()) | not(assert_vstart(0)) | not(valid_eew_emul(SEW_widen, LMUL_pow_widen))
}

/* g. Normal check for floating-point instructions */
val illegal_fp_normal : (regidx, bits(1), {|8, 16, 32, 64|}, bits(3)) -> bool
function illegal_fp_normal(vd, vm, SEW, rm_3b) = {
  not(valid_vtype()) | not(valid_rd_mask(vd, vm)) | not(valid_fp_op(SEW, rm_3b))
}

/* h. Masked check for floating-point instructions encoded with vm = 0 */
val illegal_fp_vd_masked : (regidx, {|8, 16, 32, 64|}, bits(3)) -> bool
function illegal_fp_vd_masked(vd, SEW, rm_3b) = {
  not(valid_vtype()) | vd == 0b00000 | not(valid_fp_op(SEW, rm_3b))
}

/* i. Unmasked check for floating-point instructions encoded with vm = 1 */
val illegal_fp_vd_unmasked : ({|8, 16, 32, 64|}, bits(3)) -> bool
function illegal_fp_vd_unmasked(SEW, rm_3b) = {
  not(valid_vtype()) | not(valid_fp_op(SEW, rm_3b))
}

/* j. Variable width check for floating-point widening/narrowing instructions */
val illegal_fp_variable_width : (regidx, bits(1), {|8, 16, 32, 64|}, bits(3), int, int) -> bool
function illegal_fp_variable_width(vd, vm, SEW, rm_3b, SEW_new, LMUL_pow_new) = {
  not(valid_vtype()) | not(valid_rd_mask(vd, vm)) | not(valid_fp_op(SEW, rm_3b)) |
  not(valid_eew_emul(SEW_new, LMUL_pow_new))
}

/* k. Normal check for floating-point reduction instructions */
val illegal_fp_reduction : ({|8, 16, 32, 64|}, bits(3)) -> bool
function illegal_fp_reduction(SEW, rm_3b) = {
  not(valid_vtype()) | not(assert_vstart(0)) | not(valid_fp_op(SEW, rm_3b))
}

/* l. Variable width check for floating-point widening reduction instructions */
val illegal_fp_reduction_widen : ({|8, 16, 32, 64|}, bits(3), int, int) -> bool
function illegal_fp_reduction_widen(SEW, rm_3b, SEW_widen, LMUL_pow_widen) = {
  not(valid_vtype()) | not(assert_vstart(0)) | not(valid_fp_op(SEW, rm_3b)) |
  not(valid_eew_emul(SEW_widen, LMUL_pow_widen))
}

/* m. Non-indexed load instruction check */
val illegal_load : (regidx, bits(1), int, int, int) -> bool
function illegal_load(vd, vm, nf, EEW, EMUL_pow) = {
  not(valid_vtype()) | not(valid_rd_mask(vd, vm)) |
  not(valid_eew_emul(EEW, EMUL_pow)) | not(valid_segment(nf, EMUL_pow))
}

/* n. Non-indexed store instruction check (with vs3 rather than vd) */
val illegal_store : (int, int, int) -> bool
function illegal_store(nf, EEW, EMUL_pow) = {
  not(valid_vtype()) | not(valid_eew_emul(EEW, EMUL_pow)) | not(valid_segment(nf, EMUL_pow))
}

/* o. Indexed load instruction check */
val illegal_indexed_load : (regidx, bits(1), int, int, int, int) -> bool
function illegal_indexed_load(vd, vm, nf, EEW_index, EMUL_pow_index, EMUL_pow_data) = {
  not(valid_vtype()) | not(valid_rd_mask(vd, vm)) |
  not(valid_eew_emul(EEW_index, EMUL_pow_index)) | not(valid_segment(nf, EMUL_pow_data))
}

/* p. Indexed store instruction check (with vs3 rather than vd) */
val illegal_indexed_store : (int, int, int, int) -> bool
function illegal_indexed_store(nf, EEW_index, EMUL_pow_index, EMUL_pow_data) = {
  not(valid_vtype()) | not(valid_eew_emul(EEW_index, EMUL_pow_index)) |
  not(valid_segment(nf, EMUL_pow_data))
}

/* Scalar register shaping */
val get_scalar : forall 'm, 'm >= 8. (regidx, int('m)) -> bits('m)
function get_scalar(rs1, SEW) = {
  if SEW <= sizeof(xlen) then {
    /* Least significant SEW bits */
    X(rs1, rs_1)[SEW - 1 .. 0]
  } else {
    /* Sign extend to SEW */
    sign_extend(SEW, X(rs1, rs_1))
  }
}

/* Get the starting element index from csr vtype */
val get_start_element : unit -> nat
function get_start_element() = {
  let start_element = unsigned(vstart);
  let VLEN_pow = get_vlen_pow();
  let SEW_pow = get_sew_pow();
  /* The use of vstart values greater than the largest element
    index for the current SEW setting is reserved.
    It is recommended that implementations trap if vstart is out of bounds.
    It is not required to trap, as a possible future use of upper vstart bits
    is to store imprecise trap information. */
  if start_element > (2 ^ (3 + VLEN_pow - SEW_pow) - 1) then handle_illegal();
  start_element
}

/* Get the ending element index from csr vl */
val get_end_element : unit -> int
function get_end_element() = unsigned(vl) - 1

/* Mask handling; creates a pre-masked result vector for vstart, vl, vta/vma, and vm */
/* vm should be baked into vm_val from doing read_vmask */
/* tail masking when lmul < 1 is handled in write_vreg */
/* Returns two vectors:
 *   vector1 is the result vector with values applied to masked elements
 *   vector2 is a "mask" vector that is true for an element if the corresponding element
 *     in the result vector should be updated by the calling instruction
 */
val init_masked_result : forall 'n 'm 'p, 'n >= 0. (int('n), int('m), int('p), vector('n, dec, bits('m)), vector('n, dec, bool)) -> (vector('n, dec, bits('m)), vector('n, dec, bool))
function init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val) = {
  let start_element = get_start_element();
  let end_element   = get_end_element();
  let tail_ag : agtype = get_vtype_vta();
  let mask_ag : agtype = get_vtype_vma();
  mask : vector('n, dec, bool) = undefined;
  result : vector('n, dec, bits('m)) = undefined;

  /* Determine the actual number of elements when lmul < 1 */
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / int_power(2, 0 - LMUL_pow);
  assert(num_elem >= real_num_elem);

  foreach (i from 0 to (num_elem - 1)) {
    if i < start_element then {
      /* Prestart elements defined by vstart */
      result[i] = vd_val[i];
      mask[i] = false
    } else if i > end_element then {
      /* Tail elements defined by vl */
      result[i] = match tail_ag {
        UNDISTURBED => vd_val[i],
        AGNOSTIC    => vd_val[i] /* TODO: configuration support */
      };
      mask[i] = false
    } else if i >= real_num_elem then {
      /* Tail elements defined by lmul < 1 */
      result[i] = match tail_ag {
        UNDISTURBED => vd_val[i],
        AGNOSTIC    => vd_val[i] /* TODO: configuration support */
      };
      mask[i] = false
    } else if not(vm_val[i]) then {
      /* Inactive body elements defined by vm */
      result[i] = match mask_ag {
        UNDISTURBED => vd_val[i],
        AGNOSTIC    => vd_val[i] /* TODO: configuration support */
      };
      mask[i] = false
    } else {
      /* Active body elements */
      mask[i] = true;
    }
  };

  (result, mask)
}

/* For instructions like vector reduction and vector store,
 * masks on prestart, inactive and tail elements only affect the validation of source register elements
 * (vs3 for store and vs2 for reduction). There's no destination register to be masked.
 * In these cases, this function can be called to simply get the mask vector for vs (without the prepared vd result vector).
 */
val init_masked_source : forall 'n 'p, 'n >= 0. (int('n), int('p), vector('n, dec, bool)) -> vector('n, dec, bool)
function init_masked_source(num_elem, LMUL_pow, vm_val) = {
  let start_element = get_start_element();
  let end_element   = get_end_element();
  mask : vector('n, dec, bool) = undefined;

  /* Determine the actual number of elements when lmul < 1 */
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / int_power(2, 0 - LMUL_pow);
  assert(num_elem >= real_num_elem);

  foreach (i from 0 to (num_elem - 1)) {
    if i < start_element then {
      /* Prestart elements defined by vstart */
      mask[i] = false
    } else if i > end_element then {
      /* Tail elements defined by vl */
      mask[i] = false
    } else if i >= real_num_elem then {
      /* Tail elements defined by lmul < 1 */
      mask[i] = false
    } else if not(vm_val[i]) then {
      /* Inactive body elements defined by vm */
      mask[i] = false
    } else {
      /* Active body elements */
      mask[i] = true;
    }
  };

  mask
}

/* Mask handling for carry functions that use masks as input/output */
/* Only prestart and tail elements are masked in a mask value */
val init_masked_result_carry : forall 'n 'm 'p, 'n >= 0. (int('n), int('m), int('p), vector('n, dec, bool)) -> (vector('n, dec, bool), vector('n, dec, bool))
function init_masked_result_carry(num_elem, SEW, LMUL_pow, vd_val) = {
  let start_element = get_start_element();
  let end_element   = get_end_element();
  mask : vector('n, dec, bool) = undefined;
  result : vector('n, dec, bool) = undefined;

  /* Determine the actual number of elements when lmul < 1 */
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / int_power(2, 0 - LMUL_pow);
  assert(num_elem >= real_num_elem);

  foreach (i from 0 to (num_elem - 1)) {
    if i < start_element then {
      /* Prestart elements defined by vstart */
      result[i] = vd_val[i];
      mask[i] = false
    } else if i > end_element then {
      /* Tail elements defined by vl */
      /* Mask tail is always agnostic */
      result[i] = vd_val[i]; /* TODO: configuration support */
      mask[i] = false
    } else if i >= real_num_elem then {
      /* Tail elements defined by lmul < 1 */
      /* Mask tail is always agnostic */
      result[i] = vd_val[i]; /* TODO: configuration support */
      mask[i] = false
    } else {
      /* Active body elements */
      mask[i] = true
    }
  };

  (result, mask)
}

/* Mask handling for cmp functions that use masks as output */
val init_masked_result_cmp : forall 'n 'm 'p, 'n >= 0. (int('n), int('m), int('p), vector('n, dec, bool), vector('n, dec, bool)) -> (vector('n, dec, bool), vector('n, dec, bool))
function init_masked_result_cmp(num_elem, SEW, LMUL_pow, vd_val, vm_val) = {
  let start_element = get_start_element();
  let end_element   = get_end_element();
  let mask_ag : agtype = get_vtype_vma();
  mask : vector('n, dec, bool) = undefined;
  result : vector('n, dec, bool) = undefined;

  /* Determine the actual number of elements when lmul < 1 */
  let real_num_elem = if LMUL_pow >= 0 then num_elem else num_elem / int_power(2, 0 - LMUL_pow);
  assert(num_elem >= real_num_elem);

  foreach (i from 0 to (num_elem - 1)) {
    if i < start_element then {
      /* Prestart elements defined by vstart */
      result[i] = vd_val[i];
      mask[i] = false
    } else if i > end_element then {
      /* Tail elements defined by vl */
      /* Mask tail is always agnostic */
      result[i] = vd_val[i]; /* TODO: configuration support */
      mask[i] = false
    } else if i >= real_num_elem then {
      /* Tail elements defined by lmul < 1 */
      /* Mask tail is always agnostic */
      result[i] = vd_val[i]; /* TODO: configuration support */
      mask[i] = false
    } else if not(vm_val[i]) then {
      /* Inactive body elements defined by vm */
      result[i] = match mask_ag {
        UNDISTURBED => vd_val[i],
        AGNOSTIC    => vd_val[i] /* TODO: configuration support */
      };
      mask[i] = false
    } else {
      /* Active body elements */
      mask[i] = true
    }
  };

  (result, mask)
}

/* For vector load/store segment instructions:
 *   Read multiple register groups and concatenate them in parallel
 *   The whole segments with the same element index are combined together
 */
val read_vreg_seg : forall 'n 'm 'p 'q, 'n >= 0 & 'q >= 0. (int('n), int('m), int('p), int('q), regidx) -> vector('n, dec, bits('q * 'm))
function read_vreg_seg(num_elem, SEW, LMUL_pow, nf, vrid) = {
  assert('q * 'm > 0);
  let LMUL_reg : int = if LMUL_pow <= 0 then 1 else int_power(2, LMUL_pow);
  vreg_list : vector('q, dec, vector('n, dec, bits('m))) = undefined;
  result : vector('n, dec, bits('q * 'm)) = undefined;
  foreach (j from 0 to (nf - 1)) {
    vreg_list[j] = read_vreg(num_elem, SEW, LMUL_pow, vrid + to_bits(5, j * LMUL_reg));
  };
  foreach (i from 0 to (num_elem - 1)) {
    result[i] = zeros('q * 'm);
    foreach (j from 0 to (nf - 1)) {
      result[i] = result[i] | (zero_extend(vreg_list[j][i]) << (j * 'm))
    }
  };
  result
}

/* Floating point canonical NaN for 16-bit, 32-bit and 64-bit types */
val canonical_NaN : forall 'm, 'm in {16, 32, 64}. int('m) -> bits('m)
function canonical_NaN('m) = {
  match 'm {
    16 => canonical_NaN_H(),
    32 => canonical_NaN_S(),
    64 => canonical_NaN_D()
  }
}

/* Floating point classification functions */
val f_is_neg_inf : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_neg_inf(xf) = {
  match 'm {
    16 => f_is_neg_inf_H(xf),
    32 => f_is_neg_inf_S(xf),
    64 => f_is_neg_inf_D(xf)
  }
}

val f_is_neg_norm : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_neg_norm(xf) = {
  match 'm {
    16 => f_is_neg_norm_H(xf),
    32 => f_is_neg_norm_S(xf),
    64 => f_is_neg_norm_D(xf)
  }
}

val f_is_neg_subnorm : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_neg_subnorm(xf) = {
  match 'm {
    16 => f_is_neg_subnorm_H(xf),
    32 => f_is_neg_subnorm_S(xf),
    64 => f_is_neg_subnorm_D(xf)
  }
}

val f_is_neg_zero : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_neg_zero(xf) = {
  match 'm {
    16 => f_is_neg_zero_H(xf),
    32 => f_is_neg_zero_S(xf),
    64 => f_is_neg_zero_D(xf)
  }
}

val f_is_pos_zero : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_pos_zero(xf) = {
  match 'm {
    16 => f_is_pos_zero_H(xf),
    32 => f_is_pos_zero_S(xf),
    64 => f_is_pos_zero_D(xf)
  }
}

val f_is_pos_subnorm : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_pos_subnorm(xf) = {
  match 'm {
    16 => f_is_pos_subnorm_H(xf),
    32 => f_is_pos_subnorm_S(xf),
    64 => f_is_pos_subnorm_D(xf)
  }
}

val f_is_pos_norm : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_pos_norm(xf) = {
  match 'm {
    16 => f_is_pos_norm_H(xf),
    32 => f_is_pos_norm_S(xf),
    64 => f_is_pos_norm_D(xf)
  }
}

val f_is_pos_inf : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_pos_inf(xf) = {
  match 'm {
    16 => f_is_pos_inf_H(xf),
    32 => f_is_pos_inf_S(xf),
    64 => f_is_pos_inf_D(xf)
  }
}

val f_is_SNaN : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_SNaN(xf) = {
  match 'm {
    16 => f_is_SNaN_H(xf),
    32 => f_is_SNaN_S(xf),
    64 => f_is_SNaN_D(xf)
  }
}

val f_is_QNaN : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_QNaN(xf) = {
  match 'm {
    16 => f_is_QNaN_H(xf),
    32 => f_is_QNaN_S(xf),
    64 => f_is_QNaN_D(xf)
  }
}

val f_is_NaN : forall 'm, 'm in {16, 32, 64}. bits('m) -> bool
function f_is_NaN(xf) = {
  match 'm {
    16 => f_is_NaN_H(xf),
    32 => f_is_NaN_S(xf),
    64 => f_is_NaN_D(xf)
  }
}

/* Scalar register shaping for floating point operations */
val get_scalar_fp : forall 'n, 'n in {16, 32, 64}. (regidx, int('n)) -> bits('n)
function get_scalar_fp(rs1, SEW) = {
  assert(sizeof(flen) >= SEW, "invalid vector floating-point type width: FLEN < SEW");
  match SEW {
    16 => F_H(rs1),
    32 => F_S(rs1),
    64 => F_D(rs1)
  }
}

/* Shift amounts */
val get_shift_amount : forall 'n 'm, 0 <= 'n & 'm in {8, 16, 32, 64}. (bits('n), int('m)) -> nat
function get_shift_amount(bit_val, SEW) = {
  let lowlog2bits = log2(SEW);
  assert(0 < lowlog2bits & lowlog2bits < 'n);
  unsigned(bit_val[lowlog2bits - 1 .. 0]);
}

/* Fixed point rounding increment */
val get_fixed_rounding_incr : forall ('m 'n : Int), ('m > 0 & 'n >= 0). (bits('m), int('n)) -> bits(1)
function get_fixed_rounding_incr(vec_elem, shift_amount) = {
  if shift_amount == 0 then 0b0
  else {
    let rounding_mode = vxrm[1 .. 0];
    match rounding_mode {
      0b00 => slice(vec_elem, shift_amount - 1, 1),
      0b01 => bool_to_bits(
        (slice(vec_elem, shift_amount - 1, 1) == 0b1) & (slice(vec_elem, 0, shift_amount - 1) != zeros() | slice(vec_elem, shift_amount, 1) == 0b1)),
      0b10 => 0b0,
      0b11 => bool_to_bits(
        not(slice(vec_elem, shift_amount, 1) == 0b1) & (slice(vec_elem, 0, shift_amount) != zeros()))
    }
  }
}

/* Fixed point unsigned saturation */
val unsigned_saturation : forall ('m 'n: Int), ('n >= 'm > 1). (int('m), bits('n)) -> bits('m)
function unsigned_saturation(len, elem) = {
  if unsigned(elem) > unsigned(ones('m)) then {
    vxsat = 0b1;
    ones('m)
  } else {
    vxsat = 0b0;
    elem['m - 1 .. 0]
  }
}

/* Fixed point signed saturation */
val signed_saturation : forall ('m 'n: Int), ('n >= 'm > 1). (int('m), bits('n)) -> bits('m)
function signed_saturation(len, elem) = {
  if signed(elem) > signed(0b0 @ ones('m - 1)) then {
    vxsat = 0b1;
    0b0 @ ones('m - 1)
  } else if signed(elem) < signed(0b1 @ zeros('m - 1)) then {
    vxsat = 0b1;
    0b1 @ zeros('m - 1)
  } else {
    vxsat = 0b0;
    elem['m - 1 .. 0]
  };
}

/* Get the floating point rounding mode from csr fcsr */
val get_fp_rounding_mode : unit -> rounding_mode
function get_fp_rounding_mode() = encdec_rounding_mode(fcsr[FRM])

/* Negate a floating point number */
val negate_fp : forall 'm, 'm in {16, 32, 64}. bits('m) -> bits('m)
function negate_fp(xf) = {
  match 'm {
    16 => negate_H(xf),
    32 => negate_S(xf),
    64 => negate_D(xf)
  }
}

/* Floating point functions using softfloat interface */
val fp_add: forall 'm, 'm in {16, 32, 64}. (bits(3), bits('m), bits('m)) -> bits('m)
function fp_add(rm_3b, op1, op2) = {
  let (fflags, result_val) : (bits_fflags, bits('m)) = match 'm {
    16  => riscv_f16Add(rm_3b, op1, op2),
    32  => riscv_f32Add(rm_3b, op1, op2),
    64  => riscv_f64Add(rm_3b, op1, op2)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_sub: forall 'm, 'm in {16, 32, 64}. (bits(3), bits('m), bits('m)) -> bits('m)
function fp_sub(rm_3b, op1, op2) = {
  let (fflags, result_val) : (bits_fflags, bits('m)) = match 'm {
    16  => riscv_f16Sub(rm_3b, op1, op2),
    32  => riscv_f32Sub(rm_3b, op1, op2),
    64  => riscv_f64Sub(rm_3b, op1, op2)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_min : forall 'm, 'm in {16, 32, 64}. (bits('m), bits('m)) -> bits('m)
function fp_min(op1, op2) = {
  let (fflags, op1_lt_op2) : (bits_fflags, bool) = match 'm {
    16  => riscv_f16Lt_quiet(op1, op2),
    32  => riscv_f32Lt_quiet(op1, op2),
    64  => riscv_f64Lt_quiet(op1, op2)
  };

  let result_val = if (f_is_NaN(op1) & f_is_NaN(op2)) then canonical_NaN('m)
                else if f_is_NaN(op1) then op2
                else if f_is_NaN(op2) then op1
                else if (f_is_neg_zero(op1) & f_is_pos_zero(op2)) then op1
                else if (f_is_neg_zero(op2) & f_is_pos_zero(op1)) then op2
                else if op1_lt_op2 then op1
                else op2;
  accrue_fflags(fflags);
  result_val
}

val fp_max : forall 'm, 'm in {16, 32, 64}. (bits('m), bits('m)) -> bits('m)
function fp_max(op1, op2) = {
  let (fflags, op1_lt_op2) : (bits_fflags, bool) = match 'm {
    16  => riscv_f16Lt_quiet(op1, op2),
    32  => riscv_f32Lt_quiet(op1, op2),
    64  => riscv_f64Lt_quiet(op1, op2)
  };

  let result_val = if (f_is_NaN(op1) & f_is_NaN(op2)) then canonical_NaN('m)
                else if f_is_NaN(op1) then op2
                else if f_is_NaN(op2) then op1
                else if (f_is_neg_zero(op1) & f_is_pos_zero(op2)) then op2
                else if (f_is_neg_zero(op2) & f_is_pos_zero(op1)) then op1
                else if op1_lt_op2 then op2
                else op1;
  accrue_fflags(fflags);
  result_val
}

val fp_eq : forall 'm, 'm in {16, 32, 64}. (bits('m), bits('m)) -> bool
function fp_eq(op1, op2) = {
  let (fflags, result_val) : (bits_fflags, bool) = match 'm {
    16  => riscv_f16Eq(op1, op2),
    32  => riscv_f32Eq(op1, op2),
    64  => riscv_f64Eq(op1, op2)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_gt : forall 'm, 'm in {16, 32, 64}. (bits('m), bits('m)) -> bool
function fp_gt(op1, op2) = {
  let (fflags, temp_val) : (bits_fflags, bool) = match 'm {
    16  => riscv_f16Le(op1, op2),
    32  => riscv_f32Le(op1, op2),
    64  => riscv_f64Le(op1, op2)
  };
  let result_val = (if fflags == 0b10000 then false else not(temp_val));
  accrue_fflags(fflags);
  result_val
}

val fp_ge : forall 'm, 'm in {16, 32, 64}. (bits('m), bits('m)) -> bool
function fp_ge(op1, op2) = {
  let (fflags, temp_val) : (bits_fflags, bool) = match 'm {
    16  => riscv_f16Lt(op1, op2),
    32  => riscv_f32Lt(op1, op2),
    64  => riscv_f64Lt(op1, op2)
  };
  let result_val = (if fflags == 0b10000 then false else not(temp_val));
  accrue_fflags(fflags);
  result_val
}

val fp_lt : forall 'm, 'm in {16, 32, 64}. (bits('m), bits('m)) -> bool
function fp_lt(op1, op2) = {
  let (fflags, result_val) : (bits_fflags, bool) = match 'm {
    16  => riscv_f16Lt(op1, op2),
    32  => riscv_f32Lt(op1, op2),
    64  => riscv_f64Lt(op1, op2)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_le : forall 'm, 'm in {16, 32, 64}. (bits('m), bits('m)) -> bool
function fp_le(op1, op2) = {
  let (fflags, result_val) : (bits_fflags, bool) = match 'm {
    16  => riscv_f16Le(op1, op2),
    32  => riscv_f32Le(op1, op2),
    64  => riscv_f64Le(op1, op2)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_mul : forall 'm, 'm in {16, 32, 64}. (bits(3), bits('m), bits('m)) -> bits('m)
function fp_mul(rm_3b, op1, op2) = {
  let (fflags, result_val) : (bits_fflags, bits('m)) = match 'm {
    16  => riscv_f16Mul(rm_3b, op1, op2),
    32  => riscv_f32Mul(rm_3b, op1, op2),
    64  => riscv_f64Mul(rm_3b, op1, op2)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_div : forall 'm, 'm in {16, 32, 64}. (bits(3), bits('m), bits('m)) -> bits('m)
function fp_div(rm_3b, op1, op2) = {
  let (fflags, result_val) : (bits_fflags, bits('m)) = match 'm {
    16  => riscv_f16Div(rm_3b, op1, op2),
    32  => riscv_f32Div(rm_3b, op1, op2),
    64  => riscv_f64Div(rm_3b, op1, op2)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_muladd : forall 'm, 'm in {16, 32, 64}. (bits(3), bits('m), bits('m), bits('m)) -> bits('m)
function fp_muladd(rm_3b, op1, op2, opadd) = {
  let (fflags, result_val) : (bits_fflags, bits('m)) = match 'm {
    16  => riscv_f16MulAdd(rm_3b, op1, op2, opadd),
    32  => riscv_f32MulAdd(rm_3b, op1, op2, opadd),
    64  => riscv_f64MulAdd(rm_3b, op1, op2, opadd)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_nmuladd : forall 'm, 'm in {16, 32, 64}. (bits(3), bits('m), bits('m), bits('m)) -> bits('m)
function fp_nmuladd(rm_3b, op1, op2, opadd) = {
  let op1 = negate_fp(op1);
  let (fflags, result_val) : (bits_fflags, bits('m)) = match 'm {
    16  => riscv_f16MulAdd(rm_3b, op1, op2, opadd),
    32  => riscv_f32MulAdd(rm_3b, op1, op2, opadd),
    64  => riscv_f64MulAdd(rm_3b, op1, op2, opadd)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_mulsub : forall 'm, 'm in {16, 32, 64}. (bits(3), bits('m), bits('m), bits('m)) -> bits('m)
function fp_mulsub(rm_3b, op1, op2, opsub) = {
  let opsub = negate_fp(opsub);
  let (fflags, result_val) : (bits_fflags, bits('m)) = match 'm {
    16  => riscv_f16MulAdd(rm_3b, op1, op2, opsub),
    32  => riscv_f32MulAdd(rm_3b, op1, op2, opsub),
    64  => riscv_f64MulAdd(rm_3b, op1, op2, opsub)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_nmulsub : forall 'm, 'm in {16, 32, 64}. (bits(3), bits('m), bits('m), bits('m)) -> bits('m)
function fp_nmulsub(rm_3b, op1, op2, opsub) = {
  let opsub = negate_fp(opsub);
  let op1 = negate_fp(op1);
  let (fflags, result_val) : (bits_fflags, bits('m)) = match 'm {
    16  => riscv_f16MulAdd(rm_3b, op1, op2, opsub),
    32  => riscv_f32MulAdd(rm_3b, op1, op2, opsub),
    64  => riscv_f64MulAdd(rm_3b, op1, op2, opsub)
  };
  accrue_fflags(fflags);
  result_val
}

val fp_class : forall 'm, 'm in {16, 32, 64}. bits('m) -> bits('m)
function fp_class(xf) = {
  let result_val_10b : bits(10) =
    if      f_is_neg_inf(xf)     then 0b_00_0000_0001
    else if f_is_neg_norm(xf)    then 0b_00_0000_0010
    else if f_is_neg_subnorm(xf) then 0b_00_0000_0100
    else if f_is_neg_zero(xf)    then 0b_00_0000_1000
    else if f_is_pos_zero(xf)    then 0b_00_0001_0000
    else if f_is_pos_subnorm(xf) then 0b_00_0010_0000
    else if f_is_pos_norm(xf)    then 0b_00_0100_0000
    else if f_is_pos_inf(xf)     then 0b_00_1000_0000
    else if f_is_SNaN(xf)        then 0b_01_0000_0000
    else if f_is_QNaN(xf)        then 0b_10_0000_0000
    else zeros();

  zero_extend(result_val_10b)
}

val fp_widen : forall 'm, 'm in {16, 32}. bits('m) -> bits('m * 2)
function fp_widen(nval) = {
  let rm_3b = fcsr[FRM];
  let (fflags, wval) : (bits_fflags, bits('m * 2)) = match 'm {
    16 => riscv_f16ToF32(rm_3b, nval),
    32 => riscv_f32ToF64(rm_3b, nval)
  };
  accrue_fflags(fflags);
  wval
}

/* Floating point functions without softfloat support */
val riscv_f16ToI16 : (bits_rm, bits_H) -> (bits_fflags, bits(16))
function riscv_f16ToI16 (rm, v) = {
  let (_, sig32) = riscv_f16ToI32(rm, v);
  if signed(sig32) > signed(0b0 @ ones(15)) then (nvFlag(), 0b0 @ ones(15))
  else if signed(sig32) < signed(0b1 @ zeros(15)) then (nvFlag(), 0b1 @ zeros(15))
  else (zeros(5), sig32[15 .. 0]);
}

val riscv_f16ToI8 : (bits_rm, bits_H) -> (bits_fflags, bits(8))
function riscv_f16ToI8 (rm, v) = {
  let (_, sig32) = riscv_f16ToI32(rm, v);
  if signed(sig32) > signed(0b0 @ ones(7)) then (nvFlag(), 0b0 @ ones(7))
  else if signed(sig32) < signed(0b1 @ zeros(7)) then (nvFlag(), 0b1 @ zeros(7))
  else (zeros(5), sig32[7 .. 0]);
}

val riscv_f32ToI16 : (bits_rm, bits_S) -> (bits_fflags, bits(16))
function riscv_f32ToI16 (rm, v) = {
  let (_, sig32) = riscv_f32ToI32(rm, v);
  if signed(sig32) > signed(0b0 @ ones(15)) then (nvFlag(), 0b0 @ ones(15))
  else if signed(sig32) < signed(0b1 @ zeros(15)) then (nvFlag(), 0b1 @ zeros(15))
  else (zeros(5), sig32[15 .. 0]);
}

val riscv_f16ToUi16 : (bits_rm, bits_H) -> (bits_fflags, bits(16))
function riscv_f16ToUi16 (rm, v) = {
  let (_, sig32) = riscv_f16ToUi32(rm, v);
  if unsigned(sig32) > unsigned(ones(16)) then (nvFlag(), ones(16))
  else (zeros(5), sig32[15 .. 0]);
}

val riscv_f16ToUi8 : (bits_rm, bits_H) -> (bits_fflags, bits(8))
function riscv_f16ToUi8 (rm, v) = {
  let (_, sig32) = riscv_f16ToUi32(rm, v);
  if unsigned(sig32) > unsigned(ones(8)) then (nvFlag(), ones(8))
  else (zeros(5), sig32[7 .. 0]);
}

val riscv_f32ToUi16 : (bits_rm, bits_S) -> (bits_fflags, bits(16))
function riscv_f32ToUi16 (rm, v) = {
  let (_, sig32) = riscv_f32ToUi32(rm, v);
  if unsigned(sig32) > unsigned(ones(16)) then (nvFlag(), ones(16))
  else (zeros(5), sig32[15 .. 0]);
}

val count_leadingzeros : (bits(64), int) -> int
function count_leadingzeros (sig, len) = {
  idx : int = -1;
  assert(len == 10 | len == 23 | len == 52);
  foreach (i from 0 to (len - 1)) {
    if sig[i] == bitone then idx = i;
  };
  len - idx - 1
}

val rsqrt7 : forall 'm, 'm in {16, 32, 64}. (bits('m), bool) -> bits_D
function rsqrt7 (v, sub) = {
  let (sig, exp, sign, e, s) : (bits(64), bits(64), bits(1), nat, nat) = match 'm {
    16 => (zero_extend(64, v[9 .. 0]), zero_extend(64, v[14 .. 10]), [v[15]], 5, 10),
    32 => (zero_extend(64, v[22 .. 0]), zero_extend(64, v[30 .. 23]), [v[31]], 8, 23),
    64 => (zero_extend(64, v[51 .. 0]), zero_extend(64, v[62 .. 52]), [v[63]], 11, 52)
  };
  assert(s == 10 & e == 5 | s == 23 & e == 8 | s == 52 & e == 11);
  let table : vector(128, dec, int) = [
      52, 51, 50, 48, 47, 46, 44, 43,
      42, 41, 40, 39, 38, 36, 35, 34,
      33, 32, 31, 30, 30, 29, 28, 27,
      26, 25, 24, 23, 23, 22, 21, 20,
      19, 19, 18, 17, 16, 16, 15, 14,
      14, 13, 12, 12, 11, 10, 10, 9,
      9, 8, 7, 7, 6, 6, 5, 4,
      4, 3, 3, 2, 2, 1, 1, 0,
      127, 125, 123, 121, 119, 118, 116, 114,
      113, 111, 109, 108, 106, 105, 103, 102,
      100, 99, 97, 96, 95, 93, 92, 91,
      90, 88, 87, 86, 85, 84, 83, 82,
      80, 79, 78, 77, 76, 75, 74, 73,
      72, 71, 70, 70, 69, 68, 67, 66,
      65, 64, 63, 63, 62, 61, 60, 59,
      59, 58, 57, 56, 56, 55, 54, 53];

  let (normalized_exp, normalized_sig) =
      if sub then {
        let nr_leadingzeros = count_leadingzeros(sig, s);
        assert(nr_leadingzeros >= 0);
        (to_bits(64, (0 - nr_leadingzeros)), zero_extend(64, sig[(s - 1) .. 0] << (1 + nr_leadingzeros)))
      } else {
        (exp, sig)
      };

  let idx : nat = match 'm {
    16 => unsigned([normalized_exp[0]] @ normalized_sig[9 .. 4]),
    32 => unsigned([normalized_exp[0]] @ normalized_sig[22 .. 17]),
    64 => unsigned([normalized_exp[0]] @ normalized_sig[51 .. 46])
  };
  assert(idx >= 0 & idx < 128);
  let out_sig = to_bits(s, table[(127 - idx)]) << (s - 7);
  let out_exp = to_bits(e, (3 * (2^(e - 1) - 1) - 1 - signed(normalized_exp)) / 2);
  zero_extend(64, sign @ out_exp @ out_sig)
}

val riscv_f16Rsqrte7 : (bits_rm, bits_H) -> (bits_fflags, bits_H)
function riscv_f16Rsqrte7 (rm, v) = {
  match fp_class(v) {
    0x0001 => (nvFlag(), 0x7e00),
    0x0002 => (nvFlag(), 0x7e00),
    0x0004 => (nvFlag(), 0x7e00),
    0x0100 => (nvFlag(), 0x7e00),
    0x0200 => (zeros(5), 0x7e00),
    0x0008 => (dzFlag(), 0xfc00),
    0x0010 => (dzFlag(), 0x7c00),
    0x0080 => (zeros(5), 0x0000),
    0x0020 => (zeros(5), rsqrt7(v, true)[15 .. 0]),
    _      => (zeros(5), rsqrt7(v, false)[15 .. 0])
  }
}

val riscv_f32Rsqrte7 : (bits_rm, bits_S) -> (bits_fflags, bits_S)
function riscv_f32Rsqrte7 (rm, v) = {
  match fp_class(v)[15 .. 0] {
    0x0001 => (nvFlag(), 0x7fc00000),
    0x0002 => (nvFlag(), 0x7fc00000),
    0x0004 => (nvFlag(), 0x7fc00000),
    0x0100 => (nvFlag(), 0x7fc00000),
    0x0200 => (zeros(5), 0x7fc00000),
    0x0008 => (dzFlag(), 0xff800000),
    0x0010 => (dzFlag(), 0x7f800000),
    0x0080 => (zeros(5), 0x00000000),
    0x0020 => (zeros(5), rsqrt7(v, true)[31 .. 0]),
    _      => (zeros(5), rsqrt7(v, false)[31 .. 0])
  }
}

val riscv_f64Rsqrte7 : (bits_rm, bits_D) -> (bits_fflags, bits_D)
function riscv_f64Rsqrte7 (rm, v) = {
  match fp_class(v)[15 .. 0] {
    0x0001 => (nvFlag(), 0x7ff8000000000000),
    0x0002 => (nvFlag(), 0x7ff8000000000000),
    0x0004 => (nvFlag(), 0x7ff8000000000000),
    0x0100 => (nvFlag(), 0x7ff8000000000000),
    0x0200 => (zeros(5), 0x7ff8000000000000),
    0x0008 => (dzFlag(), 0xfff0000000000000),
    0x0010 => (dzFlag(), 0x7ff0000000000000),
    0x0080 => (zeros(5), zeros(64)),
    0x0020 => (zeros(5), rsqrt7(v, true)[63 .. 0]),
    _      => (zeros(5), rsqrt7(v, false)[63 .. 0])
  }
}

val recip7 : forall 'm, 'm in {16, 32, 64}. (bits('m), bits(3), bool) -> (bool, bits_D)
function recip7 (v, rm_3b, sub) = {
  let (sig, exp, sign, e, s) : (bits(64), bits(64), bits(1), nat, nat) = match 'm {
    16 => (zero_extend(64, v[9 .. 0]), zero_extend(64, v[14 .. 10]), [v[15]], 5, 10),
    32 => (zero_extend(64, v[22 .. 0]), zero_extend(64, v[30 .. 23]), [v[31]], 8, 23),
    64 => (zero_extend(64, v[51 .. 0]), zero_extend(64, v[62 .. 52]), [v[63]], 11, 52)
  };
  assert(s == 10 & e == 5 | s == 23 & e == 8 | s == 52 & e == 11);
  let table : vector(128, dec, int) = [
      127, 125, 123, 121, 119, 117, 116, 114,
      112, 110, 109, 107, 105, 104, 102, 100,
      99, 97, 96, 94, 93, 91, 90, 88,
      87, 85, 84, 83, 81, 80, 79, 77,
      76, 75, 74, 72, 71, 70, 69, 68,
      66, 65, 64, 63, 62, 61, 60, 59,
      58, 57, 56, 55, 54, 53, 52, 51,
      50, 49, 48, 47, 46, 45, 44, 43,
      42, 41, 40, 40, 39, 38, 37, 36,
      35, 35, 34, 33, 32, 31, 31, 30,
      29, 28, 28, 27, 26, 25, 25, 24,
      23, 23, 22, 21, 21, 20, 19, 19,
      18, 17, 17, 16, 15, 15, 14, 14,
      13, 12, 12, 11, 11, 10, 9, 9,
      8, 8, 7, 7, 6, 5, 5, 4,
      4, 3, 3, 2, 2, 1, 1, 0];

  let nr_leadingzeros = count_leadingzeros(sig, s);
  assert(nr_leadingzeros >= 0);
  let (normalized_exp, normalized_sig) =
      if sub then {
        (to_bits(64, (0 - nr_leadingzeros)), zero_extend(64, sig[(s - 1) .. 0] << (1 + nr_leadingzeros)))
      } else {
        (exp, sig)
      };

  let idx : nat = match 'm {
    16 => unsigned(normalized_sig[9 .. 3]),
    32 => unsigned(normalized_sig[22 .. 16]),
    64 => unsigned(normalized_sig[51 .. 45])
  };
  assert(idx >= 0 & idx < 128);
  let mid_exp = to_bits(e, 2 * (2^(e - 1) - 1) - 1 - signed(normalized_exp));
  let mid_sig = to_bits(s, table[(127 - idx)]) << (s - 7);

  let (out_exp, out_sig)=
      if mid_exp == zeros(e) then {
        (mid_exp, mid_sig >> 1 | 0b1 @ zeros(s - 1))
      } else if mid_exp == ones(e) then {
        (zeros(e), mid_sig >> 2 | 0b01 @ zeros(s - 2))
      } else (mid_exp, mid_sig);

  if sub & nr_leadingzeros > 1 then {
      if (rm_3b == 0b001 | rm_3b == 0b010 & sign == 0b0 | rm_3b == 0b011 & sign == 0b1) then {
        (true, zero_extend(64, sign @ ones(e - 1) @ 0b0 @ ones(s)))
      }
      else (true, zero_extend(64, sign @ ones(e) @ zeros(s)))
    } else (false, zero_extend(64, sign @ out_exp @ out_sig))
}

val riscv_f16Recip7 : (bits_rm, bits_H) -> (bits_fflags, bits_H)
function riscv_f16Recip7 (rm, v) = {
  let (round_abnormal_true, res_true) = recip7(v, rm, true);
  let (round_abnormal_false, res_false) = recip7(v, rm, false);
  match fp_class(v) {
    0x0001 => (zeros(5), 0x8000),
    0x0080 => (zeros(5), 0x0000),
    0x0008 => (dzFlag(), 0xfc00),
    0x0010 => (dzFlag(), 0x7c00),
    0x0100 => (nvFlag(), 0x7e00),
    0x0200 => (zeros(5), 0x7e00),
    0x0004 => if round_abnormal_true then (nxFlag() | ofFlag(), res_true[15 .. 0]) else (zeros(5), res_true[15 .. 0]),
    0x0020 => if round_abnormal_true then (nxFlag() | ofFlag(), res_true[15 .. 0]) else (zeros(5), res_true[15 .. 0]),
    _      => if round_abnormal_false then (nxFlag() | ofFlag(), res_false[15 .. 0]) else (zeros(5), res_false[15 .. 0])
  }
}

val riscv_f32Recip7 : (bits_rm, bits_S) -> (bits_fflags, bits_S)
function riscv_f32Recip7 (rm, v) = {
  let (round_abnormal_true, res_true) = recip7(v, rm, true);
  let (round_abnormal_false, res_false) = recip7(v, rm, false);
  match fp_class(v)[15 .. 0] {
    0x0001 => (zeros(5), 0x80000000),
    0x0080 => (zeros(5), 0x00000000),
    0x0008 => (dzFlag(), 0xff800000),
    0x0010 => (dzFlag(), 0x7f800000),
    0x0100 => (nvFlag(), 0x7fc00000),
    0x0200 => (zeros(5), 0x7fc00000),
    0x0004 => if round_abnormal_true then (nxFlag() | ofFlag(), res_true[31 .. 0]) else (zeros(5), res_true[31 .. 0]),
    0x0020 => if round_abnormal_true then (nxFlag() | ofFlag(), res_true[31 .. 0]) else (zeros(5), res_true[31 .. 0]),
    _      => if round_abnormal_false then (nxFlag() | ofFlag(), res_false[31 .. 0]) else (zeros(5), res_false[31 .. 0])
  }
}

val riscv_f64Recip7 : (bits_rm, bits_D) -> (bits_fflags, bits_D)
function riscv_f64Recip7 (rm, v) = {
  let (round_abnormal_true, res_true) = recip7(v, rm, true);
  let (round_abnormal_false, res_false) = recip7(v, rm, false);
  match fp_class(v)[15 .. 0] {
    0x0001 => (zeros(5), 0x8000000000000000),
    0x0080 => (zeros(5), 0x0000000000000000),
    0x0008 => (dzFlag(), 0xfff0000000000000),
    0x0010 => (dzFlag(), 0x7ff0000000000000),
    0x0100 => (nvFlag(), 0x7ff8000000000000),
    0x0200 => (zeros(5), 0x7ff8000000000000),
    0x0004 => if round_abnormal_true then (nxFlag() | ofFlag(), res_true[63 .. 0]) else (zeros(5), res_true[63 .. 0]),
    0x0020 => if round_abnormal_true then (nxFlag() | ofFlag(), res_true[63 .. 0]) else (zeros(5), res_true[63 .. 0]),
    _      => if round_abnormal_false then (nxFlag() | ofFlag(), res_false[63 .. 0]) else (zeros(5), res_false[63 .. 0])
  }
}
