/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ****************************************************************** */
/* This file specifies the instructions in the 'Zicsr' extension.     */

/* ****************************************************************** */
union clause ast = CSR  : (bits(12), regidx, regidx, bool, csrop)

mapping encdec_csrop : csrop <-> bits(2) = {
  CSRRW <-> 0b01,
  CSRRS <-> 0b10,
  CSRRC <-> 0b11
}

mapping clause encdec = CSR(csr, rs1, rd, is_imm, op)
  <-> csr @ rs1 @ bool_bits(is_imm) @ encdec_csrop(op) @ rd @ 0b1110011

function readCSR csr : csreg -> xlenbits = {
  let res : xlenbits =
  match (csr, sizeof(xlen)) {
    /* machine mode */
    (0xF11,  _) => zero_extend(mvendorid),
    (0xF12,  _) => marchid,
    (0xF13,  _) => mimpid,
    (0xF14,  _) => mhartid,
    (0x300,  _) => mstatus.bits,
    (0x301,  _) => misa.bits,
    (0x302,  _) => medeleg.bits,
    (0x303,  _) => mideleg.bits,
    (0x304,  _) => mie.bits,
    (0x305,  _) => get_mtvec(),
    (0x306,  _) => zero_extend(mcounteren.bits),
    (0x30A,  _) => menvcfg.bits[sizeof(xlen) - 1 .. 0],
    (0x310, 32) => mstatush.bits,
    (0x31A, 32) => menvcfg.bits[63 .. 32],
    (0x320,  _) => zero_extend(mcountinhibit.bits),

    (0x340,  _) => mscratch,
    (0x341,  _) => get_xret_target(Machine) & pc_alignment_mask(),
    (0x342,  _) => mcause.bits,
    (0x343,  _) => mtval,
    (0x344,  _) => mip.bits,

    // pmpcfgN
    (0x3A @ idx : bits(4),  _) if idx[0] == bitzero | sizeof(xlen) == 32 => pmpReadCfgReg(unsigned(idx)),
    // pmpaddrN. Unfortunately the PMP index does not nicely align with the CSR index bits.
    (0x3B @ idx : bits(4),  _) => pmpReadAddrReg(unsigned(0b00 @ idx)),
    (0x3C @ idx : bits(4),  _) => pmpReadAddrReg(unsigned(0b01 @ idx)),
    (0x3D @ idx : bits(4),  _) => pmpReadAddrReg(unsigned(0b10 @ idx)),
    (0x3E @ idx : bits(4),  _) => pmpReadAddrReg(unsigned(0b11 @ idx)),

    /* machine mode counters */
    (0xB00,  _) => mcycle[(sizeof(xlen) - 1) .. 0],
    (0xB02,  _) => minstret[(sizeof(xlen) - 1) .. 0],
    (0xB80, 32) => mcycle[63 .. 32],
    (0xB82, 32) => minstret[63 .. 32],

    /* vector */
    (0x008, _) => zero_extend(vstart),
    (0x009, _) => zero_extend(vxsat),
    (0x00A, _) => zero_extend(vxrm),
    (0x00F, _) => zero_extend(vcsr.bits),
    (0xC20, _) => vl,
    (0xC21, _) => vtype.bits,
    (0xC22, _) => vlenb,

    /* trigger/debug */
    (0x7a0,  _) => ~(tselect),  /* this indicates we don't have any trigger support */

    /* supervisor mode */
    (0x100,  _) => lower_mstatus(mstatus).bits,
    (0x102,  _) => sedeleg.bits,
    (0x103,  _) => sideleg.bits,
    (0x104,  _) => lower_mie(mie, mideleg).bits,
    (0x105,  _) => get_stvec(),
    (0x106,  _) => zero_extend(scounteren.bits),
    (0x10A,  _) => senvcfg.bits[sizeof(xlen) - 1 .. 0],
    (0x140,  _) => sscratch,
    (0x141,  _) => get_xret_target(Supervisor) & pc_alignment_mask(),
    (0x142,  _) => scause.bits,
    (0x143,  _) => stval,
    (0x144,  _) => lower_mip(mip, mideleg).bits,
    (0x180,  _) => satp,

    /* user mode counters */
    (0xC00,  _) => mcycle[(sizeof(xlen) - 1) .. 0],
    (0xC01,  _) => mtime[(sizeof(xlen) - 1) .. 0],
    (0xC02,  _) => minstret[(sizeof(xlen) - 1) .. 0],
    (0xC80, 32) => mcycle[63 .. 32],
    (0xC81, 32) => mtime[63 .. 32],
    (0xC82, 32) => minstret[63 .. 32],

    /* user mode: Zkr */
    (0x015,  _) => read_seed_csr(),

    _           => /* check extensions */
                   match ext_read_CSR(csr) {
                     Some(res) => res,
                     None()    => { print_bits("unhandled read to CSR ", csr);
                                    zero_extend(0x0) }
                   }
  };
  if   get_config_print_reg()
  then print_reg("CSR " ^ to_str(csr) ^ " -> " ^ BitStr(res));
  res
}

function writeCSR (csr : csreg, value : xlenbits) -> unit = {
  let res : option(xlenbits) =
  match (csr, sizeof(xlen)) {
    /* machine mode */
    (0x300,  _) => { mstatus = legalize_mstatus(mstatus, value); Some(mstatus.bits) },
    (0x301,  _) => { misa = legalize_misa(misa, value); Some(misa.bits) },
    (0x302,  _) => { medeleg = legalize_medeleg(medeleg, value); Some(medeleg.bits) },
    (0x303,  _) => { mideleg = legalize_mideleg(mideleg, value); Some(mideleg.bits) },
    (0x304,  _) => { mie = legalize_mie(mie, value); Some(mie.bits) },
    (0x305,  _) => { Some(set_mtvec(value)) },
    (0x306,  _) => { mcounteren = legalize_mcounteren(mcounteren, value); Some(zero_extend(mcounteren.bits)) },
    (0x30A, 32) => { menvcfg = legalize_envcfg(menvcfg, menvcfg.bits[63 .. 32] @ value); Some(menvcfg.bits[31 .. 0]) },
    (0x30A, 64) => { menvcfg = legalize_envcfg(menvcfg, value); Some(menvcfg.bits) },
    (0x310, 32) => { Some(mstatush.bits) }, // ignore writes for now
    (0x31A, 32) => { menvcfg = legalize_envcfg(menvcfg, value @ menvcfg.bits[31 .. 0]); Some(menvcfg.bits[63 .. 32]) },
    (0x320,  _) => { mcountinhibit = legalize_mcountinhibit(mcountinhibit, value); Some(zero_extend(mcountinhibit.bits)) },
    (0x340,  _) => { mscratch = value; Some(mscratch) },
    (0x341,  _) => { Some(set_xret_target(Machine, value)) },
    (0x342,  _) => { mcause.bits = value; Some(mcause.bits) },
    (0x343,  _) => { mtval = value; Some(mtval) },
    (0x344,  _) => { mip = legalize_mip(mip, value); Some(mip.bits) },

    // pmpcfgN
    (0x3A @ idx : bits(4),  _) if idx[0] == bitzero | sizeof(xlen) == 32 => {
      let idx = unsigned(idx);
      pmpWriteCfgReg(idx, value); Some(pmpReadCfgReg(idx))
    },

    // pmpaddrN. Unfortunately the PMP index does not nicely align with the CSR index bits.
    (0x3B @ idx : bits(4),  _) => { let idx = unsigned(0b00 @ idx); pmpWriteAddrReg(idx, value); Some(pmpReadAddrReg(idx)) },
    (0x3C @ idx : bits(4),  _) => { let idx = unsigned(0b01 @ idx); pmpWriteAddrReg(idx, value); Some(pmpReadAddrReg(idx)) },
    (0x3D @ idx : bits(4),  _) => { let idx = unsigned(0b10 @ idx); pmpWriteAddrReg(idx, value); Some(pmpReadAddrReg(idx)) },
    (0x3E @ idx : bits(4),  _) => { let idx = unsigned(0b11 @ idx); pmpWriteAddrReg(idx, value); Some(pmpReadAddrReg(idx)) },

    /* machine mode counters */
    (0xB00,  _) => { mcycle[(sizeof(xlen) - 1) .. 0] = value; Some(value) },
    (0xB02,  _) => { minstret[(sizeof(xlen) - 1) .. 0] = value; minstret_increment = false; Some(value) },
    (0xB80, 32) => { mcycle[63 .. 32] = value; Some(value) },
    (0xB82, 32) => { minstret[63 .. 32] = value; minstret_increment = false; Some(value) },

    /* trigger/debug */
    (0x7a0,  _) => { tselect = value; Some(tselect) },

    /* supervisor mode */
    (0x100,  _) => { mstatus = legalize_sstatus(mstatus, value); Some(mstatus.bits) },
    (0x102,  _) => { sedeleg = legalize_sedeleg(sedeleg, value); Some(sedeleg.bits) },
    (0x103,  _) => { sideleg.bits = value; Some(sideleg.bits) }, /* TODO: does this need legalization? */
    (0x104,  _) => { mie = legalize_sie(mie, mideleg, value); Some(mie.bits) },
    (0x105,  _) => { Some(set_stvec(value)) },
    (0x106,  _) => { scounteren = legalize_scounteren(scounteren, value); Some(zero_extend(scounteren.bits)) },
    (0x10A,  _) => { senvcfg = legalize_envcfg(senvcfg, zero_extend(value)); Some(senvcfg.bits[sizeof(xlen) - 1 .. 0]) },
    (0x140,  _) => { sscratch = value; Some(sscratch) },
    (0x141,  _) => { Some(set_xret_target(Supervisor, value)) },
    (0x142,  _) => { scause.bits = value; Some(scause.bits) },
    (0x143,  _) => { stval = value; Some(stval) },
    (0x144,  _) => { mip = legalize_sip(mip, mideleg, value); Some(mip.bits) },
    (0x180,  _) => { satp = legalize_satp(cur_Architecture(), satp, value); Some(satp) },

    /* user mode: seed (entropy source). writes are ignored */
    (0x015,  _) => write_seed_csr(),

    /* vector */
    (0x008, _) => { let vstart_length = get_vlen_pow(); vstart = zero_extend(16, value[(vstart_length - 1) .. 0]); Some(zero_extend(vstart)) },
    (0x009, _) => { vxsat = value[0 .. 0]; Some(zero_extend(vxsat)) },
    (0x00A, _) => { vxrm = value[1 .. 0]; Some(zero_extend(vxrm)) },
    (0x00F, _) => { vcsr.bits = value[2 ..0]; Some(zero_extend(vcsr.bits)) },
    (0xC20, _) => { vl = value; Some(vl) },
    (0xC21, _) => { vtype.bits = value; Some(vtype.bits) },
    (0xC22, _) => { vlenb = value; Some(vlenb) },

    _           => ext_write_CSR(csr, value)
  };
  match res {
    Some(v) => if   get_config_print_reg()
               then print_reg("CSR " ^ to_str(csr) ^ " <- " ^ BitStr(v) ^ " (input: " ^ BitStr(value) ^ ")"),
    None()  => print_bits("unhandled write to CSR ", csr)
  }
}

$ifdef RVFI_DII
val rvfi_rCSR : (csreg, xlenbits) -> unit
function rvfi_rCSR (r,v) = {
  rvfi_csr_data[rvfi_csr_addr]  = zero_extend(r);
  rvfi_csr_data[rvfi_csr_rdata] = zero_extend(v);
  rvfi_csr_data_present = true;
}
$else
val rvfi_rCSR : (csreg, xlenbits) -> unit
function rvfi_rCSR (r,v) = ()
$endif

$ifdef RVFI_DII
val rvfi_wCSR : (csreg, xlenbits) -> unit
function rvfi_wCSR (r,v) = {
  rvfi_csr_data[rvfi_csr_addr]  = zero_extend(r);
  rvfi_csr_data[rvfi_csr_wdata] = zero_extend(v);
  rvfi_csr_data_present = true;
}
$else
val rvfi_wCSR : (csreg, xlenbits) -> unit
function rvfi_wCSR (r,v) = ()
$endif

function clause execute CSR(csr, rs1, rd, is_imm, op) = {
  let rs1_val : xlenbits = if is_imm then zero_extend(rs1) else X(rs1, rs_1);
  let isWrite : bool = match op {
    CSRRW  => true,
    _      => if is_imm then unsigned(rs1_val) != 0 else unsigned(rs1) != 0
  };
  if not(check_CSR(csr, cur_privilege, isWrite))
  then { handle_illegal(); RETIRE_FAIL }
  else if not(ext_check_CSR(csr, cur_privilege, isWrite))
  then { ext_check_CSR_fail(); RETIRE_FAIL }
  else {
    let csr_val = readCSR(csr); /* could have side-effects, so technically shouldn't perform for CSRW[I] with rd == 0 */
    if (unsigned(rd) != 0) then {
      rvfi_rCSR(csr, csr_val);
    };
    if isWrite then {
      let new_val : xlenbits = match op {
        CSRRW => rs1_val,
        CSRRS => csr_val | rs1_val,
        CSRRC => csr_val & ~(rs1_val)
      };
      writeCSR(csr, new_val);
      rvfi_wCSR(csr, new_val); /* call without further checks as rs1!=0 and imm!=0 checks already done for isWrite */
    };
    X(rd) = csr_val;
    RETIRE_SUCCESS
  }
}

mapping maybe_i : bool <-> string = {
  true  <-> "i",
  false <-> ""
}

mapping csr_mnemonic : csrop <-> string = {
  CSRRW <-> "csrrw",
  CSRRS <-> "csrrs",
  CSRRC <-> "csrrc"
}

mapping clause assembly = CSR(csr, rs1, rd, true, op)
  <-> csr_mnemonic(op) ^ "i" ^ spc() ^ reg_name(rd)  ^ sep() ^ csr_name_map(csr) ^ sep() ^ hex_bits_5(rs1)
mapping clause assembly = CSR(csr, rs1, rd, false, op)
  <-> csr_mnemonic(op) ^ spc() ^ reg_name(rd) ^ sep() ^ csr_name_map(csr) ^ sep() ^ reg_name(rs1)
