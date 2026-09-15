/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ****************************************************************** */
/* This file specifies the atomic instructions in the 'A' extension.  */

/* ****************************************************************** */
// Some print utils for lr/sc.

function aqrl_str(aq : bool, rl : bool) -> string =
  match (aq, rl) {
    (false, false) => "",
    (false, true)  => ".rl",
    (true, false)  => ".aq",
    (true, true)   => ".aqrl"
  }

function lrsc_width_str(width : word_width) -> string =
  match (width) {
    BYTE   => ".b",
    HALF   => ".h",
    WORD   => ".w",
    DOUBLE => ".d"
  }

/**
 * RISC-V only appears to define LR / SC / AMOs for word and double, although
 * there seem to be encodings reserved for other widths.
 */
function amo_width_valid(size : word_width) -> bool = {
  match(size) {
    WORD   => true,
    DOUBLE => sizeof(xlen) >= 64,
    _      => false
  }
}

/* ****************************************************************** */
union clause ast = LOADRES : (bool, bool, regidx, word_width, regidx)

mapping clause encdec = LOADRES(aq, rl, rs1, size, rd) if amo_width_valid(size)
  <-> 0b00010 @ bool_bits(aq) @ bool_bits(rl) @ 0b00000 @ rs1 @ 0b0 @ size_bits(size) @ rd @ 0b0101111 if amo_width_valid(size)


/* We could set load-reservations on physical or virtual addresses.
 * For now we set them on virtual addresses, since it makes the
 * sequential model of SC a bit simpler, at the cost of an explicit
 * call to load_reservation in LR and cancel_reservation in SC.
 */

val process_loadres : forall 'n, 0 < 'n <= xlen_bytes. (regidx, xlenbits, MemoryOpResult(bits(8 * 'n)), bool) -> Retired
function process_loadres(rd, addr, value, is_unsigned) =
  match extend_value(is_unsigned, value) {
    MemValue(result) => { load_reservation(addr); X(rd) = result; RETIRE_SUCCESS },
    MemException(e)  => { handle_mem_exception(addr, e); RETIRE_FAIL }
  }

function clause execute(LOADRES(aq, rl, rs1, width, rd)) = {
  if haveAtomics() then {
    /* Get the address, X(rs1) (no offset).
     * Extensions might perform additional checks on address validity.
     */
    match ext_data_get_addr(rs1, zeros(), Read(Data), width) {
      Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); RETIRE_FAIL },
      Ext_DataAddr_OK(vaddr) => {
        let aligned : bool =
           /* BYTE and HALF would only occur due to invalid decodes, but it doesn't hurt
            * to treat them as valid here; otherwise we'd need to throw an internal_error.
            */
           match width {
             BYTE   => true,
             HALF   => vaddr[0..0] == 0b0,
             WORD   => vaddr[1..0] == 0b00,
             DOUBLE => vaddr[2..0] == 0b000
           };
        /* "LR faults like a normal load, even though it's in the AMO major opcode space."
         * - Andrew Waterman, isa-dev, 10 Jul 2018.
         */
        if not(aligned)
        then { handle_mem_exception(vaddr, E_Load_Addr_Align()); RETIRE_FAIL }
        else match translateAddr(vaddr, Read(Data)) {
               TR_Failure(e, _)    => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
               TR_Address(addr, _) =>
                 match (width, sizeof(xlen)) {
                   (BYTE, _)    => process_loadres(rd, vaddr, mem_read(Read(Data), addr, 1, aq, aq & rl, true), false),
                   (HALF, _)    => process_loadres(rd, vaddr, mem_read(Read(Data), addr, 2, aq, aq & rl, true), false),
                   (WORD, _)    => process_loadres(rd, vaddr, mem_read(Read(Data), addr, 4, aq, aq & rl, true), false),
                   (DOUBLE, 64) => process_loadres(rd, vaddr, mem_read(Read(Data), addr, 8, aq, aq & rl, true), false),
                   _            => internal_error(__FILE__, __LINE__, "Unexpected AMO width")
                 }
             }
      }
    }
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

mapping clause assembly = LOADRES(aq, rl, rs1, size, rd)
  <-> "lr." ^ size_mnemonic(size) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")"

/* ****************************************************************** */
union clause ast = STORECON : (bool, bool, regidx, regidx, word_width, regidx)

mapping clause encdec = STORECON(aq, rl, rs2, rs1, size, rd) if amo_width_valid(size)
  <-> 0b00011 @ bool_bits(aq) @ bool_bits(rl) @ rs2 @ rs1 @ 0b0 @ size_bits(size) @ rd @ 0b0101111 if amo_width_valid(size)

/* NOTE: Currently, we only EA if address translation is successful. This may need revisiting. */
function clause execute (STORECON(aq, rl, rs2, rs1, width, rd)) = {
  if speculate_conditional () == false then {
    /* should only happen in rmem
     * rmem: allow SC to fail very early
     */
    X(rd) = zero_extend(0b1); RETIRE_SUCCESS
  } else {
    if haveAtomics() then {
      /* normal non-rmem case
       * rmem: SC is allowed to succeed (but might fail later)
       */
      /* Get the address, X(rs1) (no offset).
       * Extensions might perform additional checks on address validity.
       */
      match ext_data_get_addr(rs1, zeros(), Write(Data), width) {
        Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); RETIRE_FAIL },
        Ext_DataAddr_OK(vaddr) => {
          let aligned : bool =
            /* BYTE and HALF would only occur due to invalid decodes, but it doesn't hurt
             * to treat them as valid here; otherwise we'd need to throw an internal_error.
             */
            match width {
              BYTE   => true,
              HALF   => vaddr[0..0] == 0b0,
              WORD   => vaddr[1..0] == 0b00,
              DOUBLE => vaddr[2..0] == 0b000
            };
          if not(aligned)
          then { handle_mem_exception(vaddr, E_SAMO_Addr_Align()); RETIRE_FAIL }
          else {
            if match_reservation(vaddr) == false then {
              /* cannot happen in rmem */
              X(rd) = zero_extend(0b1); cancel_reservation(); RETIRE_SUCCESS
            } else {
              match translateAddr(vaddr, Write(Data)) {  /* Write and ReadWrite are equivalent here:
                                                          * both result in a SAMO exception */
                TR_Failure(e, _) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
                TR_Address(addr, _) => {
                  let eares : MemoryOpResult(unit) = match (width, sizeof(xlen)) {
                    (BYTE, _)    => mem_write_ea(addr, 1, aq & rl, rl, true),
                    (HALF, _)    => mem_write_ea(addr, 2, aq & rl, rl, true),
                    (WORD, _)    => mem_write_ea(addr, 4, aq & rl, rl, true),
                    (DOUBLE, 64) => mem_write_ea(addr, 8, aq & rl, rl, true),
                    _            => internal_error(__FILE__, __LINE__, "STORECON expected word or double")
                  };
                  match (eares) {
                    MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
                    MemValue(_) => {
                      rs2_val = X(rs2, rs_2);
                      let res : MemoryOpResult(bool) = match (width, sizeof(xlen)) {
                        (BYTE, _)    => mem_write_value(addr, 1, rs2_val[7..0], aq & rl, rl, true),
                        (HALF, _)    => mem_write_value(addr, 2, rs2_val[15..0], aq & rl, rl, true),
                        (WORD, _)    => mem_write_value(addr, 4, rs2_val[31..0], aq & rl, rl, true),
                        (DOUBLE, 64) => mem_write_value(addr, 8, rs2_val,        aq & rl, rl, true),
                        _            => internal_error(__FILE__, __LINE__, "STORECON expected word or double")
                      };
                      match (res) {
                        MemValue(true)  => { X(rd) = zero_extend(0b0); cancel_reservation(); RETIRE_SUCCESS },
                        MemValue(false) => { X(rd) = zero_extend(0b1); cancel_reservation(); RETIRE_SUCCESS },
                        MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    } else {
      handle_illegal();
      RETIRE_FAIL
    }
  }
}

mapping clause assembly = STORECON(aq, rl, rs2, rs1, size, rd)
  <-> "sc." ^ size_mnemonic(size) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs2) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")"

/* ****************************************************************** */
union clause ast = AMO : (amoop, bool, bool, regidx, regidx, word_width, regidx)

mapping encdec_amoop : amoop <-> bits(5) = {
  AMOSWAP <-> 0b00001,
  AMOADD  <-> 0b00000,
  AMOXOR  <-> 0b00100,
  AMOAND  <-> 0b01100,
  AMOOR   <-> 0b01000,
  AMOMIN  <-> 0b10000,
  AMOMAX  <-> 0b10100,
  AMOMINU <-> 0b11000,
  AMOMAXU <-> 0b11100
}

mapping clause encdec = AMO(op, aq, rl, rs2, rs1, size, rd) if amo_width_valid(size)
  <-> encdec_amoop(op) @ bool_bits(aq) @ bool_bits(rl) @ rs2 @ rs1 @ 0b0 @ size_bits(size) @ rd @ 0b0101111 if amo_width_valid(size)

/* NOTE: Currently, we only EA if address translation is successful.
   This may need revisiting. */
function clause execute (AMO(op, aq, rl, rs2, rs1, width, rd)) = {
  if haveAtomics() then {
    /* Get the address, X(rs1) (no offset).
     * Some extensions perform additional checks on address validity.
     */
    match ext_data_get_addr(rs1, zeros(), ReadWrite(Data, Data), width) {
      Ext_DataAddr_Error(e)  => { ext_handle_data_check_error(e); RETIRE_FAIL },
      Ext_DataAddr_OK(vaddr) => {
        match translateAddr(vaddr, ReadWrite(Data, Data)) {
          TR_Failure(e, _) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
          TR_Address(addr, _) => {
            let eares : MemoryOpResult(unit) = match (width, sizeof(xlen)) {
              (BYTE, _)    => mem_write_ea(addr, 1, aq & rl, rl, true),
              (HALF, _)    => mem_write_ea(addr, 2, aq & rl, rl, true),
              (WORD, _)    => mem_write_ea(addr, 4, aq & rl, rl, true),
              (DOUBLE, 64) => mem_write_ea(addr, 8, aq & rl, rl, true),
              _            => internal_error(__FILE__, __LINE__, "Unexpected AMO width")
            };
            let is_unsigned : bool = match op {
              AMOMINU => true,
              AMOMAXU => true,
              _       => false
            };
            let rs2_val : xlenbits = match width {
              BYTE   => if is_unsigned then zero_extend(X(rs2, rs_2)[7..0])  else sign_extend(X(rs2, rs_2)[7..0]),
              HALF   => if is_unsigned then zero_extend(X(rs2, rs_2)[15..0]) else sign_extend(X(rs2, rs_2)[15..0]),
              WORD   => if is_unsigned then zero_extend(X(rs2, rs_2)[31..0]) else sign_extend(X(rs2, rs_2)[31..0]),
              DOUBLE => X(rs2, rs_2)
            };
            match (eares) {
              MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
              MemValue(_) => {
                let mval : MemoryOpResult(xlenbits) = match (width, sizeof(xlen)) {
                  (BYTE, _)    => extend_value(is_unsigned, mem_read(ReadWrite(Data, Data), addr, 1, aq, aq & rl, true)),
                  (HALF, _)    => extend_value(is_unsigned, mem_read(ReadWrite(Data, Data), addr, 2, aq, aq & rl, true)),
                  (WORD, _)    => extend_value(is_unsigned, mem_read(ReadWrite(Data, Data), addr, 4, aq, aq & rl, true)),
                  (DOUBLE, 64) => extend_value(is_unsigned, mem_read(ReadWrite(Data, Data), addr, 8, aq, aq & rl, true)),
                  _            => internal_error(__FILE__, __LINE__, "Unexpected AMO width")
                };
                match (mval) {
                  MemException(e)  => { handle_mem_exception(vaddr, e); RETIRE_FAIL },
                  MemValue(loaded) => {
                    let result : xlenbits =
                      match op {
                        AMOSWAP => rs2_val,
                        AMOADD  => rs2_val + loaded,
                        AMOXOR  => rs2_val ^ loaded,
                        AMOAND  => rs2_val & loaded,
                        AMOOR   => rs2_val | loaded,

                        /* These operations convert bitvectors to integer values using [un]signed,
                         * and back using to_bits().
                         */
                        AMOMIN  => to_bits(sizeof(xlen), min(signed(rs2_val),   signed(loaded))),
                        AMOMAX  => to_bits(sizeof(xlen), max(signed(rs2_val),   signed(loaded))),
                        AMOMINU => to_bits(sizeof(xlen), min(unsigned(rs2_val), unsigned(loaded))),
                        AMOMAXU => to_bits(sizeof(xlen), max(unsigned(rs2_val), unsigned(loaded)))
                      };
                    let rval : xlenbits = match width {
                      BYTE   => sign_extend(loaded[7..0]),
                      HALF   => sign_extend(loaded[15..0]),
                      WORD   => sign_extend(loaded[31..0]),
                      DOUBLE => loaded
                    };
                    let wval : MemoryOpResult(bool) = match (width, sizeof(xlen)) {
                      (BYTE, _)    => mem_write_value(addr, 1, result[7..0],  aq & rl, rl, true),
                      (HALF, _)    => mem_write_value(addr, 2, result[15..0], aq & rl, rl, true),
                      (WORD, _)    => mem_write_value(addr, 4, result[31..0], aq & rl, rl, true),
                      (DOUBLE, 64) => mem_write_value(addr, 8, result,        aq & rl, rl, true),
                      _            => internal_error(__FILE__, __LINE__, "Unexpected AMO width")
                    };
                    match (wval) {
                      MemValue(true)  => { X(rd) = rval; RETIRE_SUCCESS },
                      MemValue(false) => { internal_error(__FILE__, __LINE__, "AMO got false from mem_write_value") },
                      MemException(e) => { handle_mem_exception(vaddr, e); RETIRE_FAIL }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  } else {
    handle_illegal();
    RETIRE_FAIL
  }
}

mapping amo_mnemonic : amoop <-> string = {
  AMOSWAP <-> "amoswap",
  AMOADD  <-> "amoadd",
  AMOXOR  <-> "amoxor",
  AMOAND  <-> "amoand",
  AMOOR   <-> "amoor",
  AMOMIN  <-> "amomin",
  AMOMAX  <-> "amomax",
  AMOMINU <-> "amominu",
  AMOMAXU <-> "amomaxu"
}

mapping clause assembly = AMO(op, aq, rl, rs2, rs1, width, rd)
  <-> amo_mnemonic(op) ^ "." ^ size_mnemonic(width) ^ maybe_aq(aq) ^ maybe_rl(rl) ^ spc() ^ reg_name(rd) ^ sep() ^ reg_name(rs2) ^ sep() ^ "(" ^ reg_name(rs1) ^ ")"
