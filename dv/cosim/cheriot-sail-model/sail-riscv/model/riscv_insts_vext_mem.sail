/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ******************************************************************************* */
/* This file implements part of the vector extension.                              */
/* Chapter 7: Vector Loads and Stores                                              */
/* ******************************************************************************* */

mapping nfields_int : bits(3) <-> {|1, 2, 3, 4, 5, 6, 7, 8|} = {
  0b000     <-> 1,
  0b001     <-> 2,
  0b010     <-> 3,
  0b011     <-> 4,
  0b100     <-> 5,
  0b101     <-> 6,
  0b110     <-> 7,
  0b111     <-> 8
}

mapping nfields_string : bits(3) <-> string = {
  0b000     <-> "",
  0b001     <-> "seg2",
  0b010     <-> "seg3",
  0b011     <-> "seg4",
  0b100     <-> "seg5",
  0b101     <-> "seg6",
  0b110     <-> "seg7",
  0b111     <-> "seg8"
}

mapping vlewidth_bitsnumberstr : vlewidth <-> string = {
  VLE8      <-> "8",
  VLE16     <-> "16",
  VLE32     <-> "32",
  VLE64     <-> "64"
}

mapping encdec_vlewidth : vlewidth <-> bits(3) = {
  VLE8      <-> 0b000,
  VLE16     <-> 0b101,
  VLE32     <-> 0b110,
  VLE64     <-> 0b111
}

mapping vlewidth_bytesnumber : vlewidth <-> {|1, 2, 4, 8|} = {
  VLE8      <-> 1,
  VLE16     <-> 2,
  VLE32     <-> 4,
  VLE64     <-> 8
}

mapping vlewidth_pow : vlewidth <-> {|3, 4, 5, 6|} = {
  VLE8      <-> 3,
  VLE16     <-> 4,
  VLE32     <-> 5,
  VLE64     <-> 6
}

mapping bytes_wordwidth : {|1, 2, 4, 8|} <-> word_width = {
  1 <-> BYTE,
  2 <-> HALF,
  4 <-> WORD,
  8 <-> DOUBLE
}

/* ******************** Vector Load Unit-Stride Normal & Segment (mop=0b00, lumop=0b00000) ********************* */
union clause ast = VLSEGTYPE : (bits(3), bits(1), regidx, vlewidth, regidx)

mapping clause encdec = VLSEGTYPE(nf, vm, rs1, width, vd) if haveVExt()
  <-> nf @ 0b0 @ 0b00 @ vm @ 0b00000 @ rs1 @ encdec_vlewidth(width) @ vd @ 0b0000111 if haveVExt()

val process_vlseg : forall 'f 'b 'n 'p, (0 < 'f & 'f <= 8) & ('b in {1, 2, 4, 8}) & ('n >= 0). (int('f), bits(1), regidx, int('b), regidx, int('p), int('n)) -> Retired
function process_vlseg (nf, vm, vd, load_width_bytes, rs1, EMUL_pow, num_elem) = {
  let EMUL_reg : int = if EMUL_pow <= 0 then 1 else int_power(2, EMUL_pow);
  let width_type : word_width = bytes_wordwidth(load_width_bytes);
  let vm_val : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vd_seg : vector('n, dec, bits('f * 'b * 8)) = read_vreg_seg(num_elem, load_width_bytes * 8, EMUL_pow, nf, vd);

  let (result, mask) = init_masked_result(num_elem, nf * load_width_bytes * 8, EMUL_pow, vd_seg, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then { /* active segments */
      vstart = to_bits(16, i);
      foreach (j from 0 to (nf - 1)) {
        let elem_offset = (i * nf + j) * load_width_bytes;
        match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Read(Data), width_type) {
          Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
          Ext_DataAddr_OK(vaddr) =>
              if check_misaligned(vaddr, width_type)
              then { handle_mem_exception(vaddr, E_Load_Addr_Align()); return RETIRE_FAIL }
              else match translateAddr(vaddr, Read(Data)) {
                TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
                TR_Address(paddr, _) => {
                  match mem_read(Read(Data), paddr, load_width_bytes, false, false, false) {
                    MemValue(elem)   => write_single_element(load_width_bytes * 8, i, vd + to_bits(5, j * EMUL_reg), elem),
                    MemException(e)  => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                  }
                }
              }
        }
      }
    } else { /* prestart, masked or tail segments */
      foreach (j from 0 to (nf - 1)) {
        let skipped_elem = (result[i] >> (j * load_width_bytes * 8))[(load_width_bytes * 8 - 1) .. 0];
        write_single_element(load_width_bytes * 8, i, vd + to_bits(5, j * EMUL_reg), skipped_elem)
      }
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VLSEGTYPE(nf, vm, rs1, width, vd)) = {
  let load_width_bytes = vlewidth_bytesnumber(width);
  let EEW = load_width_bytes * 8;
  let EEW_pow = vlewidth_pow(width);
  let SEW_pow = get_sew_pow();
  let LMUL_pow = get_lmul_pow();
  let EMUL_pow = EEW_pow - SEW_pow + LMUL_pow;
  let num_elem = get_num_elem(EMUL_pow, EEW); /* # of element of each register group */
  let nf_int = nfields_int(nf);

  if illegal_load(vd, vm, nf_int, EEW, EMUL_pow) then { handle_illegal(); return RETIRE_FAIL };

  process_vlseg(nf_int, vm, vd, load_width_bytes, rs1, EMUL_pow, num_elem)
}

mapping clause assembly = VLSEGTYPE(nf, vm, rs1, width, vd)
  <-> "vl" ^ nfields_string(nf) ^ "e" ^ vlewidth_bitsnumberstr(width) ^ ".v" ^ spc() ^ vreg_name(vd) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")" ^ maybe_vmask(vm)

/* ************ Vector Load Unit-Stride Normal & Segment Fault-Only-First (mop=0b00, lumop=0b10000) ************ */
union clause ast = VLSEGFFTYPE : (bits(3), bits(1), regidx, vlewidth, regidx)

mapping clause encdec = VLSEGFFTYPE(nf, vm, rs1, width, vd) if haveVExt()
  <-> nf @ 0b0 @ 0b00 @ vm @ 0b10000 @ rs1 @ encdec_vlewidth(width) @ vd @ 0b0000111 if haveVExt()

val process_vlsegff : forall 'f 'b 'n 'p, (0 < 'f & 'f <= 8) & ('b in {1, 2, 4, 8}) & ('n >= 0). (int('f), bits(1), regidx, int('b), regidx, int('p), int('n)) -> Retired
function process_vlsegff (nf, vm, vd, load_width_bytes, rs1, EMUL_pow, num_elem) = {
  let EMUL_reg : int = if EMUL_pow <= 0 then 1 else int_power(2, EMUL_pow);
  let width_type : word_width = bytes_wordwidth(load_width_bytes);
  let vm_val : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vd_seg : vector('n, dec, bits('f * 'b * 8)) = read_vreg_seg(num_elem, load_width_bytes * 8, EMUL_pow, nf, vd);
  let tail_ag : agtype = get_vtype_vta();

  let (result, mask) = init_masked_result(num_elem, nf * load_width_bytes * 8, EMUL_pow, vd_seg, vm_val);

  trimmed : bool = false;
  foreach (i from 0 to (num_elem - 1)) {
    if not(trimmed) then {
      if vm_val[i] then { /* active segments */
        foreach (j from 0 to (nf - 1)) {
          let elem_offset = (i * nf + j) * load_width_bytes;
          match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Read(Data), width_type) {
            Ext_DataAddr_Error(e)  => {
              if i == 0 then { ext_handle_data_check_error(e); return RETIRE_FAIL }
              else {
                vl = to_bits(sizeof(xlen), i);
                print_reg("CSR vl <- " ^ BitStr(vl));
                trimmed = true
              }
            },
            Ext_DataAddr_OK(vaddr) => {
              if check_misaligned(vaddr, width_type) then {
                if i == 0 then { handle_mem_exception(vaddr, E_Load_Addr_Align()); return RETIRE_FAIL }
                else {
                  vl = to_bits(sizeof(xlen), i);
                  print_reg("CSR vl <- " ^ BitStr(vl));
                  trimmed = true
                }
              } else match translateAddr(vaddr, Read(Data)) {
                TR_Failure(e, _)     => {
                  if i == 0 then { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                  else {
                    vl = to_bits(sizeof(xlen), i);
                    print_reg("CSR vl <- " ^ BitStr(vl));
                    trimmed = true
                  }
                },
                TR_Address(paddr, _) => {
                  match mem_read(Read(Data), paddr, load_width_bytes, false, false, false) {
                    MemValue(elem)   => write_single_element(load_width_bytes * 8, i, vd + to_bits(5, j * EMUL_reg), elem),
                    MemException(e)  => {
                      if i == 0 then { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                      else {
                        vl = to_bits(sizeof(xlen), i);
                        print_reg("CSR vl <- " ^ BitStr(vl));
                        trimmed = true
                      }
                    }
                  }
                }
              }
            }
          }
        }
      } else { /* prestart, masked or tail segments */
        foreach (j from 0 to (nf - 1)) {
          let skipped_elem = (result[i] >> (j * load_width_bytes * 8))[(load_width_bytes * 8 - 1) .. 0];
          write_single_element(load_width_bytes * 8, i, vd + to_bits(5, j * EMUL_reg), skipped_elem)
        }
      }
    } else {
      /* if vl is trimmed, elements past the new vl are treated as tail elements */
      if tail_ag == AGNOSTIC then {
        foreach (j from 0 to (nf - 1)) {
          let skipped_elem = (vd_seg[i] >> (j * load_width_bytes * 8))[(load_width_bytes * 8 - 1) .. 0];
          write_single_element(load_width_bytes * 8, i, vd + to_bits(5, j * EMUL_reg), skipped_elem)
        }
        /* TODO: configuration support for agnostic behavior */
      }
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VLSEGFFTYPE(nf, vm, rs1, width, vd)) = {
  let load_width_bytes = vlewidth_bytesnumber(width);
  let EEW = load_width_bytes * 8;
  let EEW_pow = vlewidth_pow(width);
  let SEW_pow = get_sew_pow();
  let LMUL_pow = get_lmul_pow();
  let EMUL_pow = EEW_pow - SEW_pow + LMUL_pow;
  let num_elem = get_num_elem(EMUL_pow, EEW);
  let nf_int = nfields_int(nf);

  if illegal_load(vd, vm, nf_int, EEW, EMUL_pow) then { handle_illegal(); return RETIRE_FAIL };

  process_vlsegff(nf_int, vm, vd, load_width_bytes, rs1, EMUL_pow, num_elem)
}

mapping clause assembly = VLSEGFFTYPE(nf, vm, rs1, width, vd)
  <-> "vl" ^ nfields_string(nf) ^ "e" ^ vlewidth_bitsnumberstr(width) ^ "ff.v" ^ spc() ^ vreg_name(vd) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")" ^ maybe_vmask(vm)

/* ******************** Vector Store Unit-Stride Normal & Segment (mop=0b00, sumop=0b00000) ******************** */
union clause ast = VSSEGTYPE : (bits(3), bits(1), regidx, vlewidth, regidx)

mapping clause encdec = VSSEGTYPE(nf, vm, rs1, width, vs3) if haveVExt()
  <-> nf @ 0b0 @ 0b00 @ vm @ 0b00000 @ rs1 @ encdec_vlewidth(width) @ vs3 @ 0b0100111 if haveVExt()

val process_vsseg : forall 'f 'b 'n 'p, (0 < 'f & 'f <= 8) & ('b in {1, 2, 4, 8}) & ('n >= 0). (int('f), bits(1), regidx, int('b), regidx, int('p), int('n)) -> Retired
function process_vsseg (nf, vm, vs3, load_width_bytes, rs1, EMUL_pow, num_elem) = {
  let EMUL_reg : int = if EMUL_pow <= 0 then 1 else int_power(2, EMUL_pow);
  let width_type : word_width = bytes_wordwidth(load_width_bytes);
  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vs3_seg : vector('n, dec, bits('f * 'b * 8)) = read_vreg_seg(num_elem, load_width_bytes * 8, EMUL_pow, nf, vs3);
  let mask    : vector('n, dec, bool) = init_masked_source(num_elem, EMUL_pow, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if vm_val[i] then { /* active segments */
      vstart = to_bits(16, i);
      foreach (j from 0 to (nf - 1)) {
        let elem_offset = (i * nf + j) * load_width_bytes;
        match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Write(Data), width_type) {
          Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
          Ext_DataAddr_OK(vaddr) =>
            if check_misaligned(vaddr, width_type)
            then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); return RETIRE_FAIL }
            else match translateAddr(vaddr, Write(Data)) {
              TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
              TR_Address(paddr, _) => {
                let eares : MemoryOpResult(unit) = mem_write_ea(paddr, load_width_bytes, false, false, false);
                match (eares) {
                  MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
                  MemValue(_) => {
                    let elem_val : bits('b * 8) = read_single_element(load_width_bytes * 8, i, vs3 + to_bits(5, j * EMUL_reg));
                    let res : MemoryOpResult(bool) = mem_write_value(paddr, load_width_bytes, elem_val, false, false, false);
                    match (res) {
                      MemValue(true)  => (),
                      MemValue(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
                      MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                    }
                  }
                }
              }
            }
        }
      }
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VSSEGTYPE(nf, vm, rs1, width, vs3)) = {
  let load_width_bytes = vlewidth_bytesnumber(width);
  let EEW = load_width_bytes * 8;
  let EEW_pow = vlewidth_pow(width);
  let SEW_pow = get_sew_pow();
  let LMUL_pow = get_lmul_pow();
  let EMUL_pow = EEW_pow - SEW_pow + LMUL_pow;
  let num_elem = get_num_elem(EMUL_pow, EEW);
  let nf_int = nfields_int(nf);

  if illegal_store(nf_int, EEW, EMUL_pow) then { handle_illegal(); return RETIRE_FAIL };

  process_vsseg(nf_int, vm, vs3, load_width_bytes, rs1, EMUL_pow, num_elem)
}

mapping clause assembly = VSSEGTYPE(nf, vm, rs1, width, vs3)
  <-> "vs" ^ nfields_string(nf) ^ "e" ^ vlewidth_bitsnumberstr(width) ^ ".v" ^ spc() ^ vreg_name(vs3) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")" ^ maybe_vmask(vm)

/* ****************************** Vector Load Strided Normal & Segment (mop=0b10) ****************************** */
union clause ast = VLSSEGTYPE : (bits(3), bits(1), regidx, regidx, vlewidth, regidx)

mapping clause encdec = VLSSEGTYPE(nf, vm, rs2, rs1, width, vd) if haveVExt()
  <-> nf @ 0b0 @ 0b10 @ vm @ rs2 @ rs1 @ encdec_vlewidth(width) @ vd @ 0b0000111 if haveVExt()

val process_vlsseg : forall 'f 'b 'n 'p, (0 < 'f & 'f <= 8) & ('b in {1, 2, 4, 8}) & ('n >= 0). (int('f), bits(1), regidx, int('b), regidx, regidx, int('p), int('n)) -> Retired
function process_vlsseg (nf, vm, vd, load_width_bytes, rs1, rs2, EMUL_pow, num_elem) = {
  let EMUL_reg : int = if EMUL_pow <= 0 then 1 else int_power(2, EMUL_pow);
  let width_type : word_width = bytes_wordwidth(load_width_bytes);
  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vd_seg  : vector('n, dec, bits('f * 'b * 8)) = read_vreg_seg(num_elem, load_width_bytes * 8, EMUL_pow, nf, vd);
  let rs2_val : int = signed(get_scalar(rs2, sizeof(xlen)));

  let (result, mask) = init_masked_result(num_elem, nf * load_width_bytes * 8, EMUL_pow, vd_seg, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then { /* active segments */
      vstart = to_bits(16, i);
      foreach (j from 0 to (nf - 1)) {
        let elem_offset = i * rs2_val + j * load_width_bytes;
        match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Read(Data), width_type) {
          Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
          Ext_DataAddr_OK(vaddr) =>
            if check_misaligned(vaddr, width_type)
            then { handle_mem_exception(vaddr, E_Load_Addr_Align()); return RETIRE_FAIL }
            else match translateAddr(vaddr, Read(Data)) {
              TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
              TR_Address(paddr, _) => {
                match mem_read(Read(Data), paddr, load_width_bytes, false, false, false) {
                  MemValue(elem)   => write_single_element(load_width_bytes * 8, i, vd + to_bits(5, j * EMUL_reg), elem),
                  MemException(e)  => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                }
              }
            }
        }
      }
    } else { /* prestart, masked or tail segments */
      foreach (j from 0 to (nf - 1)) {
        let skipped_elem = (result[i] >> (j * load_width_bytes * 8))[(load_width_bytes * 8 - 1) .. 0];
        write_single_element(load_width_bytes * 8, i, vd + to_bits(5, j * EMUL_reg), skipped_elem)
      }
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VLSSEGTYPE(nf, vm, rs2, rs1, width, vd)) = {
  let load_width_bytes = vlewidth_bytesnumber(width);
  let EEW = load_width_bytes * 8;
  let EEW_pow = vlewidth_pow(width);
  let SEW_pow = get_sew_pow();
  let LMUL_pow = get_lmul_pow();
  let EMUL_pow = EEW_pow - SEW_pow + LMUL_pow;
  let num_elem = get_num_elem(EMUL_pow, EEW);
  let nf_int = nfields_int(nf);

  if illegal_load(vd, vm, nf_int, EEW, EMUL_pow) then { handle_illegal(); return RETIRE_FAIL };

  process_vlsseg(nf_int, vm, vd, load_width_bytes, rs1, rs2, EMUL_pow, num_elem)
}

mapping clause assembly = VLSSEGTYPE(nf, vm, rs2, rs1, width, vd)
  <-> "vls" ^ nfields_string(nf) ^ "e" ^ vlewidth_bitsnumberstr(width) ^ ".v" ^ spc() ^ vreg_name(vd) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")" ^ sep() ^ reg_name(rs2) ^ maybe_vmask(vm)

/* ***************************** Vector Store Strided Normal & Segment (mop=0b10) ****************************** */
union clause ast = VSSSEGTYPE : (bits(3), bits(1), regidx, regidx, vlewidth, regidx)

mapping clause encdec = VSSSEGTYPE(nf, vm, rs2, rs1, width, vs3) if haveVExt()
  <-> nf @ 0b0 @ 0b10 @ vm @ rs2 @ rs1 @ encdec_vlewidth(width) @ vs3 @ 0b0100111 if haveVExt()

val process_vssseg : forall 'f 'b 'n 'p, (0 < 'f & 'f <= 8) & ('b in {1, 2, 4, 8}) & ('n >= 0). (int('f), bits(1), regidx, int('b), regidx, regidx, int('p), int('n)) -> Retired
function process_vssseg (nf, vm, vs3, load_width_bytes, rs1, rs2, EMUL_pow, num_elem) = {
  let EMUL_reg : int = if EMUL_pow <= 0 then 1 else int_power(2, EMUL_pow);
  let width_type : word_width = bytes_wordwidth(load_width_bytes);
  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vs3_seg : vector('n, dec, bits('f * 'b * 8)) = read_vreg_seg(num_elem, load_width_bytes * 8, EMUL_pow, nf, vs3);
  let rs2_val : int = signed(get_scalar(rs2, sizeof(xlen)));
  let mask    : vector('n, dec, bool) = init_masked_source(num_elem, EMUL_pow, vm_val);

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then { /* active segments */
      vstart = to_bits(16, i);
      foreach (j from 0 to (nf - 1)) {
        let elem_offset = i * rs2_val + j * load_width_bytes;
        match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Write(Data), width_type) {
          Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
          Ext_DataAddr_OK(vaddr) =>
            if check_misaligned(vaddr, width_type)
            then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); return RETIRE_FAIL }
            else match translateAddr(vaddr, Write(Data)) {
              TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
              TR_Address(paddr, _) => {
                let eares : MemoryOpResult(unit) = mem_write_ea(paddr, load_width_bytes, false, false, false);
                match (eares) {
                  MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
                  MemValue(_) => {
                    let elem_val : bits('b * 8) = read_single_element(load_width_bytes * 8, i, vs3 + to_bits(5, j * EMUL_reg));
                    let res : MemoryOpResult(bool) = mem_write_value(paddr, load_width_bytes, elem_val, false, false, false);
                    match (res) {
                      MemValue(true)  => (),
                      MemValue(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
                      MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                    }
                  }
                }
              }
            }
        }
      }
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VSSSEGTYPE(nf, vm, rs2, rs1, width, vs3)) = {
  let load_width_bytes = vlewidth_bytesnumber(width);
  let EEW = load_width_bytes * 8;
  let EEW_pow = vlewidth_pow(width);
  let SEW_pow = get_sew_pow();
  let LMUL_pow = get_lmul_pow();
  let EMUL_pow = EEW_pow - SEW_pow + LMUL_pow;
  let num_elem = get_num_elem(EMUL_pow, EEW);
  let nf_int = nfields_int(nf);

  if illegal_store(nf_int, EEW, EMUL_pow) then { handle_illegal(); return RETIRE_FAIL };

  process_vssseg(nf_int, vm, vs3, load_width_bytes, rs1, rs2, EMUL_pow, num_elem)
}

mapping clause assembly = VSSSEGTYPE(nf, vm, rs2, rs1, width, vs3)
  <-> "vss" ^ nfields_string(nf) ^ "e" ^ vlewidth_bitsnumberstr(width) ^ ".v" ^ spc() ^ vreg_name(vs3) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")" ^ sep() ^ reg_name(rs2) ^ maybe_vmask(vm)

/* ************************* Vector Load Indexed Unordered Normal & Segment (mop=0b01) ************************* */
union clause ast = VLUXSEGTYPE : (bits(3), bits(1), regidx, regidx, vlewidth, regidx)

mapping clause encdec = VLUXSEGTYPE(nf, vm, vs2, rs1, width, vd) if haveVExt()
  <-> nf @ 0b0 @ 0b01 @ vm @ vs2 @ rs1 @ encdec_vlewidth(width) @ vd @ 0b0000111 if haveVExt()

val process_vlxseg : forall 'f 'ib 'db 'ip 'dp 'n, (0 < 'f & 'f <= 8) & ('ib in {1, 2, 4, 8}) & ('db in {1, 2, 4, 8}) & ('n >= 0). (int('f), bits(1), regidx, int('ib), int('db), int('ip), int('dp), regidx, regidx, int('n), int) -> Retired
function process_vlxseg (nf, vm, vd, EEW_index_bytes, EEW_data_bytes, EMUL_index_pow, EMUL_data_pow, rs1, vs2, num_elem, mop) = {
  let EMUL_data_reg : int = if EMUL_data_pow <= 0 then 1 else int_power(2, EMUL_data_pow);
  let width_type : word_width = bytes_wordwidth(EEW_data_bytes);
  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vd_seg  : vector('n, dec, bits('f * 'db * 8)) = read_vreg_seg(num_elem, EEW_data_bytes * 8, EMUL_data_pow, nf, vd);
  let vs2_val : vector('n, dec, bits('ib * 8)) = read_vreg(num_elem, EEW_index_bytes * 8, EMUL_index_pow, vs2);

  let (result, mask) = init_masked_result(num_elem, nf * EEW_data_bytes * 8, EMUL_data_pow, vd_seg, vm_val);

  /* currently mop = 1 (unordered) or 3 (ordered) do the same operations */
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then { /* active segments */
      vstart = to_bits(16, i);
      foreach (j from 0 to (nf - 1)) {
        let elem_offset : int = signed(vs2_val[i]) + j * EEW_data_bytes;
        match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Read(Data), width_type) {
          Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
          Ext_DataAddr_OK(vaddr) =>
            if check_misaligned(vaddr, width_type)
            then { handle_mem_exception(vaddr, E_Load_Addr_Align()); return RETIRE_FAIL }
            else match translateAddr(vaddr, Read(Data)) {
              TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
              TR_Address(paddr, _) => {
                match mem_read(Read(Data), paddr, EEW_data_bytes, false, false, false) {
                  MemValue(elem)   => write_single_element(EEW_data_bytes * 8, i, vd + to_bits(5, j * EMUL_data_reg), elem),
                  MemException(e)  => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                }
              }
            }
        }
      }
    } else { /* prestart, masked or tail segments */
      foreach (j from 0 to (nf - 1)) {
        let skipped_elem = (result[i] >> (j * EEW_data_bytes * 8))[(EEW_data_bytes * 8 - 1) .. 0];
        write_single_element(EEW_data_bytes * 8, i, vd + to_bits(5, j * EMUL_data_reg), skipped_elem)
      }
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VLUXSEGTYPE(nf, vm, vs2, rs1, width, vd)) = {
  let EEW_index_pow = vlewidth_pow(width);
  let EEW_index_bytes = vlewidth_bytesnumber(width);
  let EEW_data_pow = get_sew_pow();
  let EEW_data_bytes = get_sew_bytes();
  let EMUL_data_pow = get_lmul_pow();
  let EMUL_index_pow = EEW_index_pow - EEW_data_pow + EMUL_data_pow;
  let num_elem = get_num_elem(EMUL_data_pow, EEW_data_bytes * 8);
  let nf_int = nfields_int(nf);

  if illegal_indexed_load(vd, vm, nf_int, EEW_index_bytes * 8, EMUL_index_pow, EMUL_data_pow) then { handle_illegal(); return RETIRE_FAIL };

  process_vlxseg(nf_int, vm, vd, EEW_index_bytes, EEW_data_bytes, EMUL_index_pow, EMUL_data_pow, rs1, vs2, num_elem, 1)
}

mapping clause assembly = VLUXSEGTYPE(nf, vm, vs2, rs1, width, vd)
  <-> "vlux" ^ nfields_string(nf) ^ "ei" ^ vlewidth_bitsnumberstr(width) ^ ".v" ^ spc() ^ vreg_name(vd) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")" ^ sep() ^ reg_name(vs2) ^ maybe_vmask(vm)

/* ************************** Vector Load Indexed Ordered Normal & Segment (mop=0b11) ************************** */
union clause ast = VLOXSEGTYPE : (bits(3), bits(1), regidx, regidx, vlewidth, regidx)

mapping clause encdec = VLOXSEGTYPE(nf, vm, vs2, rs1, width, vd) if haveVExt()
  <-> nf @ 0b0 @ 0b11 @ vm @ vs2 @ rs1 @ encdec_vlewidth(width) @ vd @ 0b0000111 if haveVExt()

function clause execute(VLOXSEGTYPE(nf, vm, vs2, rs1, width, vd)) = {
  let EEW_index_pow = vlewidth_pow(width);
  let EEW_index_bytes = vlewidth_bytesnumber(width);
  let EEW_data_pow = get_sew_pow();
  let EEW_data_bytes = get_sew_bytes();
  let EMUL_data_pow = get_lmul_pow();
  let EMUL_index_pow = EEW_index_pow - EEW_data_pow + EMUL_data_pow;
  let num_elem = get_num_elem(EMUL_data_pow, EEW_data_bytes * 8);
  let nf_int = nfields_int(nf);

  if illegal_indexed_load(vd, vm, nf_int, EEW_index_bytes * 8, EMUL_index_pow, EMUL_data_pow) then { handle_illegal(); return RETIRE_FAIL };

  process_vlxseg(nf_int, vm, vd, EEW_index_bytes, EEW_data_bytes, EMUL_index_pow, EMUL_data_pow, rs1, vs2, num_elem, 3)
}

mapping clause assembly = VLOXSEGTYPE(nf, vm, vs2, rs1, width, vd)
  <-> "vlox" ^ nfields_string(nf) ^ "ei" ^ vlewidth_bitsnumberstr(width) ^ ".v" ^ spc() ^ vreg_name(vd) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")" ^ sep() ^ reg_name(vs2) ^ maybe_vmask(vm)

/* ************************ Vector Store Indexed Unordered Normal & Segment (mop=0b01) ************************* */
union clause ast = VSUXSEGTYPE : (bits(3), bits(1), regidx, regidx, vlewidth, regidx)

mapping clause encdec = VSUXSEGTYPE(nf, vm, vs2, rs1, width, vs3) if haveVExt()
  <-> nf @ 0b0 @ 0b01 @ vm @ vs2 @ rs1 @ encdec_vlewidth(width) @ vs3 @ 0b0100111 if haveVExt()

val process_vsxseg : forall 'f 'ib 'db 'ip 'dp 'n, (0 < 'f & 'f <= 8) & ('ib in {1, 2, 4, 8}) & ('db in {1, 2, 4, 8}) & ('n >= 0). (int('f), bits(1), regidx, int('ib), int('db), int('ip), int('dp), regidx, regidx, int('n), int) -> Retired
function process_vsxseg (nf, vm, vs3, EEW_index_bytes, EEW_data_bytes, EMUL_index_pow, EMUL_data_pow, rs1, vs2, num_elem, mop) = {
  let EMUL_data_reg : int = if EMUL_data_pow <= 0 then 1 else int_power(2, EMUL_data_pow);
  let width_type : word_width = bytes_wordwidth(EEW_data_bytes);
  let vm_val  : vector('n, dec, bool) = read_vmask(num_elem, vm, 0b00000);
  let vs3_seg : vector('n, dec, bits('f * 'db * 8)) = read_vreg_seg(num_elem, EEW_data_bytes * 8, EMUL_data_pow, nf, vs3);
  let vs2_val : vector('n, dec, bits('ib * 8)) = read_vreg(num_elem, EEW_index_bytes * 8, EMUL_index_pow, vs2);
  let mask    : vector('n, dec, bool) = init_masked_source(num_elem, EMUL_data_pow, vm_val);

  /* currently mop = 1 (unordered) or 3 (ordered) do the same operations */
  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] then { /* active segments */
      vstart = to_bits(16, i);
      foreach (j from 0 to (nf - 1)) {
        let elem_offset : int = signed(vs2_val[i]) + j * EEW_data_bytes;
        match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Write(Data), width_type) {
          Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
          Ext_DataAddr_OK(vaddr) =>
            if check_misaligned(vaddr, width_type)
            then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); return RETIRE_FAIL }
            else match translateAddr(vaddr, Write(Data)) {
              TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
              TR_Address(paddr, _) => {
                let eares : MemoryOpResult(unit) = mem_write_ea(paddr, EEW_data_bytes, false, false, false);
                match (eares) {
                  MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
                  MemValue(_) => {
                    let elem_val : bits('db * 8) = read_single_element(EEW_data_bytes * 8, i, vs3 + to_bits(5, j * EMUL_data_reg));
                    let res : MemoryOpResult(bool) = mem_write_value(paddr, EEW_data_bytes, elem_val, false, false, false);
                    match (res) {
                      MemValue(true)  => (),
                      MemValue(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
                      MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                    }
                  }
                }
              }
            }
        }
      }
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VSUXSEGTYPE(nf, vm, vs2, rs1, width, vs3)) = {
  let EEW_index_pow = vlewidth_pow(width);
  let EEW_index_bytes = vlewidth_bytesnumber(width);
  let EEW_data_pow = get_sew_pow();
  let EEW_data_bytes = get_sew_bytes();
  let EMUL_data_pow = get_lmul_pow();
  let EMUL_index_pow = EEW_index_pow - EEW_data_pow + EMUL_data_pow;
  let num_elem = get_num_elem(EMUL_data_pow, EEW_data_bytes * 8); /* number of data and indices are the same */
  let nf_int = nfields_int(nf);

  if illegal_indexed_store(nf_int, EEW_index_bytes * 8, EMUL_index_pow, EMUL_data_pow) then { handle_illegal(); return RETIRE_FAIL };

  process_vsxseg(nf_int, vm, vs3, EEW_index_bytes, EEW_data_bytes, EMUL_index_pow, EMUL_data_pow, rs1, vs2, num_elem, 1)
}

mapping clause assembly = VSUXSEGTYPE(nf, vm, vs2, rs1, width, vs3)
  <-> "vsux" ^ nfields_string(nf) ^ "ei" ^ vlewidth_bitsnumberstr(width) ^ ".v" ^ spc() ^ vreg_name(vs3) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")" ^ sep() ^ reg_name(vs2) ^ maybe_vmask(vm)

/* ************************* Vector Store Indexed Ordered Normal & Segment (mop=0b11) ************************** */
union clause ast = VSOXSEGTYPE : (bits(3), bits(1), regidx, regidx, vlewidth, regidx)

mapping clause encdec = VSOXSEGTYPE(nf, vm, vs2, rs1, width, vs3) if haveVExt()
  <-> nf @ 0b0 @ 0b11 @ vm @ vs2 @ rs1 @ encdec_vlewidth(width) @ vs3 @ 0b0100111 if haveVExt()

function clause execute(VSOXSEGTYPE(nf, vm, vs2, rs1, width, vs3)) = {
  let EEW_index_pow = vlewidth_pow(width);
  let EEW_index_bytes = vlewidth_bytesnumber(width);
  let EEW_data_pow = get_sew_pow();
  let EEW_data_bytes = get_sew_bytes();
  let EMUL_data_pow = get_lmul_pow();
  let EMUL_index_pow = EEW_index_pow - EEW_data_pow + EMUL_data_pow;
  let num_elem = get_num_elem(EMUL_data_pow, EEW_data_bytes * 8); /* number of data and indices are the same */
  let nf_int = nfields_int(nf);

  if illegal_indexed_store(nf_int, EEW_index_bytes * 8, EMUL_index_pow, EMUL_data_pow) then { handle_illegal(); return RETIRE_FAIL };

  process_vsxseg(nf_int, vm, vs3, EEW_index_bytes, EEW_data_bytes, EMUL_index_pow, EMUL_data_pow, rs1, vs2, num_elem, 3)
}

mapping clause assembly = VSUXSEGTYPE(nf, vm, vs2, rs1, width, vs3)
  <-> "vsox" ^ nfields_string(nf) ^ "ei" ^ vlewidth_bitsnumberstr(width) ^ ".v" ^ spc() ^ vreg_name(vs3) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")" ^ sep() ^ reg_name(vs2) ^ maybe_vmask(vm)

/* ***************** Vector Load Unit-Stride Whole Register (vm=0b1, mop=0b00, lumop=0b01000) ****************** */
union clause ast = VLRETYPE : (bits(3), regidx, vlewidth, regidx)

mapping clause encdec = VLRETYPE(nf, rs1, width, vd) if haveVExt()
  <-> nf @ 0b0 @ 0b00 @ 0b1 @ 0b01000 @ rs1 @ encdec_vlewidth(width) @ vd @ 0b0000111 if haveVExt()

val process_vlre : forall 'f 'b 'n, ('f in {1, 2, 4, 8}) & ('b in {1, 2, 4, 8}) & ('n >= 0). (int('f), regidx, int('b), regidx, int('n)) -> Retired
function process_vlre (nf, vd, load_width_bytes, rs1, elem_per_reg) = {
  let width_type : word_width = bytes_wordwidth(load_width_bytes);
  let start_element = get_start_element();
  if start_element >= nf * elem_per_reg then return RETIRE_SUCCESS; /* no elements are written if vstart >= evl */
  let elem_to_align : int = start_element % elem_per_reg;
  cur_field : int = start_element / elem_per_reg;
  cur_elem  : int = start_element;

  if elem_to_align > 0 then {
    foreach (i from elem_to_align to (elem_per_reg - 1)) {
      vstart = to_bits(16, cur_elem);
      let elem_offset = cur_elem * load_width_bytes;
      match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Read(Data), width_type) {
        Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
        Ext_DataAddr_OK(vaddr) =>
          if check_misaligned(vaddr, width_type)
          then { handle_mem_exception(vaddr, E_Load_Addr_Align()); return RETIRE_FAIL }
          else match translateAddr(vaddr, Read(Data)) {
            TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
            TR_Address(paddr, _) => {
              match mem_read(Read(Data), paddr, load_width_bytes, false, false, false) {
                MemValue(elem)   => write_single_element(load_width_bytes * 8, i, vd + to_bits(5, cur_field), elem),
                MemException(e)  => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
              }
            }
          }
      };
      cur_elem = cur_elem + 1
    };
    cur_field = cur_field + 1
  };

  foreach (j from cur_field to (nf - 1)) {
    foreach (i from 0 to (elem_per_reg - 1)) {
      vstart = to_bits(16, cur_elem);
      let elem_offset = cur_elem * load_width_bytes;
      match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Read(Data), width_type) {
        Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
        Ext_DataAddr_OK(vaddr) =>
          if check_misaligned(vaddr, width_type)
          then { handle_mem_exception(vaddr, E_Load_Addr_Align()); return RETIRE_FAIL }
          else match translateAddr(vaddr, Read(Data)) {
            TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
            TR_Address(paddr, _) => {
              match mem_read(Read(Data), paddr, load_width_bytes, false, false, false) {
                MemValue(elem)   => write_single_element(load_width_bytes * 8, i, vd + to_bits(5, j), elem),
                MemException(e)  => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
              }
            }
          }
      };
      cur_elem = cur_elem + 1
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VLRETYPE(nf, rs1, width, vd)) = {
  let load_width_bytes = vlewidth_bytesnumber(width);
  let EEW = load_width_bytes * 8;
  let VLEN = unsigned(vlenb) * 8;
  let elem_per_reg : int = VLEN / EEW;
  let nf_int = nfields_int(nf);

  assert(elem_per_reg >= 0);
  if not(nf_int == 1 | nf_int == 2 | nf_int == 4 | nf_int == 8) then { handle_illegal(); return RETIRE_FAIL };

  process_vlre(nf_int, vd, load_width_bytes, rs1, elem_per_reg)
}

mapping clause assembly = VLRETYPE(nf, rs1, width, vd)
  <-> "vl" ^ nfields_string(nf) ^ "re" ^ vlewidth_bitsnumberstr(width) ^ ".v" ^ spc() ^ vreg_name(vd) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")"

/* ***************** Vector Store Unit-Stride Whole Register (vm=0b1, mop=0b00, lumop=0b01000) ***************** */
union clause ast = VSRETYPE : (bits(3), regidx, regidx)

mapping clause encdec = VSRETYPE(nf, rs1, vs3) if haveVExt()
  <-> nf @ 0b0 @ 0b00 @ 0b1 @ 0b01000 @ rs1 @ 0b000 @ vs3 @ 0b0100111 if haveVExt()

val process_vsre : forall 'f 'b 'n, ('f in {1, 2, 4, 8}) & ('b in {1, 2, 4, 8}) & ('n >= 0). (int('f), int('b), regidx, regidx, int('n)) -> Retired
function process_vsre (nf, load_width_bytes, rs1, vs3, elem_per_reg) = {
  let width_type : word_width = BYTE;
  let start_element = get_start_element();
  if start_element >= nf * elem_per_reg then return RETIRE_SUCCESS; /* no elements are written if vstart >= evl */
  let elem_to_align : int = start_element % elem_per_reg;
  cur_field : int = start_element / elem_per_reg;
  cur_elem  : int = start_element;

  if elem_to_align > 0 then {
    foreach (i from elem_to_align to (elem_per_reg - 1)) {
      vstart = to_bits(16, cur_elem);
      let elem_offset : int = cur_elem * load_width_bytes;
      match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Write(Data), width_type) {
        Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
        Ext_DataAddr_OK(vaddr) =>
          if check_misaligned(vaddr, width_type)
          then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); return RETIRE_FAIL }
          else match translateAddr(vaddr, Write(Data)) {
            TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
            TR_Address(paddr, _) => {
              let eares : MemoryOpResult(unit) = mem_write_ea(paddr, load_width_bytes, false, false, false);
              match (eares) {
                MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
                MemValue(_) => {
                  let elem : bits('b * 8) = read_single_element(load_width_bytes * 8, i, vs3 + to_bits(5, cur_field));
                  let res : MemoryOpResult(bool) = mem_write_value(paddr, load_width_bytes, elem, false, false, false);
                  match (res) {
                    MemValue(true)  => (),
                    MemValue(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
                    MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                  }
                }
              }
            }
          }
      };
      cur_elem = cur_elem + 1
    };
    cur_field = cur_field + 1
  };

  foreach (j from cur_field to (nf - 1)) {
    let vs3_val : vector('n, dec, bits('b * 8)) = read_vreg(elem_per_reg, load_width_bytes * 8, 0, vs3 + to_bits(5, j));
    foreach (i from 0 to (elem_per_reg - 1)) {
      vstart = to_bits(16, cur_elem);
      let elem_offset = cur_elem * load_width_bytes;
      match ext_data_get_addr(rs1, to_bits(sizeof(xlen), elem_offset), Write(Data), width_type) {
        Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
        Ext_DataAddr_OK(vaddr) =>
          if check_misaligned(vaddr, width_type)
          then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); return RETIRE_FAIL }
          else match translateAddr(vaddr, Write(Data)) {
            TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
            TR_Address(paddr, _) => {
              let eares : MemoryOpResult(unit) = mem_write_ea(paddr, load_width_bytes, false, false, false);
              match (eares) {
                MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
                MemValue(_) => {
                  let res : MemoryOpResult(bool) = mem_write_value(paddr, load_width_bytes, vs3_val[i], false, false, false);
                  match (res) {
                    MemValue(true)  => (),
                    MemValue(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
                    MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                  }
                }
              }
            }
          }
      };
      cur_elem = cur_elem + 1
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VSRETYPE(nf, rs1, vs3)) = {
  let load_width_bytes = 1;
  let EEW = 8;
  let VLEN = unsigned(vlenb) * 8;
  let elem_per_reg : int = VLEN / EEW;
  let nf_int = nfields_int(nf);

  assert(elem_per_reg >= 0);
  if not(nf_int == 1 | nf_int == 2 | nf_int == 4 | nf_int == 8) then { handle_illegal(); return RETIRE_FAIL };

  process_vsre(nf_int, load_width_bytes, rs1, vs3, elem_per_reg)
}

mapping clause assembly = VSRETYPE(nf, rs1, vs3)
  <-> "vs" ^ nfields_string(nf) ^ "r.v" ^ spc() ^ vreg_name(vs3) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")"

/* ************** Vector Mask Load/Store Unit-Stride (nf=0b000, mop=0b00, lumop or sumop=0b01011) ************** */
union clause ast = VMTYPE : (regidx, regidx, vmlsop)

mapping encdec_lsop : vmlsop <-> bits(7) = {
  VLM      <-> 0b0000111,
  VSM      <-> 0b0100111
}

mapping clause encdec = VMTYPE(rs1, vd_or_vs3, op) if haveVExt()
  <-> 0b000 @ 0b0 @ 0b00 @ 0b1 @ 0b01011 @ rs1 @ 0b000 @ vd_or_vs3 @ encdec_lsop(op) if haveVExt()

val process_vm : forall 'n 'l, ('n >= 0 & 'l >= 0). (regidx, regidx, int('n), int('l), vmlsop) -> Retired
function process_vm(vd_or_vs3, rs1, num_elem, evl, op) = {
  let width_type : word_width = BYTE;
  let start_element = get_start_element();
  let vd_or_vs3_val : vector('n, dec, bits(8)) = read_vreg(num_elem, 8, 0, vd_or_vs3);

  foreach (i from start_element to (num_elem - 1)) {
    if i < evl then { /* active elements */
      vstart = to_bits(16, i);
      if op == VLM then { /* load */
        match ext_data_get_addr(rs1, to_bits(sizeof(xlen), i), Read(Data), width_type) {
          Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
          Ext_DataAddr_OK(vaddr) =>
            if check_misaligned(vaddr, width_type)
            then { handle_mem_exception(vaddr, E_Load_Addr_Align()); return RETIRE_FAIL }
            else match translateAddr(vaddr, Read(Data)) {
              TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
              TR_Address(paddr, _) => {
                match mem_read(Read(Data), paddr, 1, false, false, false) {
                  MemValue(elem)   => write_single_element(8, i, vd_or_vs3, elem),
                  MemException(e)  => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                }
              }
            }
        }
      } else if op == VSM then { /* store */
        match ext_data_get_addr(rs1, to_bits(sizeof(xlen), i), Write(Data), width_type) {
          Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); return RETIRE_FAIL },
          Ext_DataAddr_OK(vaddr) =>
            if check_misaligned(vaddr, width_type)
            then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); return RETIRE_FAIL }
            else match translateAddr(vaddr, Write(Data)) {
              TR_Failure(e, _)     => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
              TR_Address(paddr, _) => {
                let eares : MemoryOpResult(unit) = mem_write_ea(paddr, 1, false, false, false);
                match (eares) {
                  MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL },
                  MemValue(_) => {
                    let res : MemoryOpResult(bool) = mem_write_value(paddr, 1, vd_or_vs3_val[i], false, false, false);
                    match (res) {
                      MemValue(true)  => (),
                      MemValue(false) => internal_error(__FILE__, __LINE__, "store got false from mem_write_value"),
                      MemException(e) => { handle_mem_exception(vaddr, e); return RETIRE_FAIL }
                    }
                  }
                }
              }
            }
        }
      }
    } else { /* tail elements for mask load, always with agnostic policy */
      if op == VLM then {
        write_single_element(8, i, vd_or_vs3, vd_or_vs3_val[i])
        /* TODO: configuration support for agnostic behavior */
      }
    }
  };

  vstart = zeros();
  RETIRE_SUCCESS
}

function clause execute(VMTYPE(rs1, vd_or_vs3, op)) = {
  let EEW = 8;
  let EMUL_pow = 0;
  let vl_val = unsigned(vl);
  let evl : int = if vl_val % 8 == 0 then vl_val / 8 else vl_val / 8 + 1; /* the effective vector length is evl=ceil(vl/8) */
  let num_elem = get_num_elem(EMUL_pow, EEW);

  if illegal_vd_unmasked() then { handle_illegal(); return RETIRE_FAIL };

  assert(evl >= 0);
  process_vm(vd_or_vs3, rs1, num_elem, evl, op)
}

mapping vmtype_mnemonic : vmlsop <-> string = {
  VLM      <-> "vlm.v",
  VSM      <-> "vsm.v"
}

mapping clause assembly = VMTYPE(rs1, vd_or_vs3, op)
  <-> vmtype_mnemonic(op) ^ spc() ^ vreg_name(vd_or_vs3) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")"
