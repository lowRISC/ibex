class snippy_asm_program_gen extends ibex_asm_program_gen;
  `uvm_object_utils(snippy_asm_program_gen)

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void gen_ebreak_handler(int hart);
    string instr[$];

    int unsigned r_mepc;
    int unsigned r_hw;
    int unsigned r_tmp;
    string lbl_32b;
    string lbl_done;

    r_mepc = cfg.gpr[0];
    r_hw   = cfg.gpr[1];
    r_tmp  = cfg.gpr[2];

    lbl_32b  = $sformatf("snippy_ebrk_32b_h%0d", hart);
    lbl_done = $sformatf("snippy_ebrk_done_h%0d", hart);

    gen_signature_handshake(instr, CORE_STATUS, EBREAK_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));

    instr = {instr,
      $sformatf("csrr  x%0d, 0x%0x", r_mepc, MEPC),
      $sformatf("lhu   x%0d, 0(x%0d)", r_hw, r_mepc),
      $sformatf("andi  x%0d, x%0d, 3", r_hw, r_hw),
      $sformatf("li    x%0d, 3", r_tmp),
      $sformatf("beq   x%0d, x%0d, %s", r_hw, r_tmp, lbl_32b),
      $sformatf("addi  x%0d, x%0d, 2", r_mepc, r_mepc),
      $sformatf("j     %s", lbl_done),
      $sformatf("%s:", lbl_32b),
      $sformatf("addi  x%0d, x%0d, 4", r_mepc, r_mepc),
      $sformatf("%s:", lbl_done),
      $sformatf("csrw  0x%0x, x%0d", MEPC, r_mepc)
    };

    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv,
                              cfg.sp, cfg.tp, instr);
    instr.push_back("mret");

    gen_section(get_label("ebreak_handler", hart), instr);
  endfunction

  virtual function void gen_illegal_instr_handler(int hart);
    string instr[$];
    int unsigned r_mepc, r_tval, r_len, r_tmp;
    string lbl_use2, lbl_use6, lbl_use8, lbl_done;
    string lbl_tval_zero, lbl_have_tval, lbl_real0;

    r_mepc = cfg.gpr[0];
    r_tval = cfg.gpr[1];
    r_len  = cfg.gpr[2];
    r_tmp  = cfg.gpr[3];

    lbl_use2      = $sformatf("snippy_ill_use2_h%0d", hart);
    lbl_use6      = $sformatf("snippy_ill_use6_h%0d", hart);
    lbl_use8      = $sformatf("snippy_ill_use8_h%0d", hart);
    lbl_done      = $sformatf("snippy_ill_done_h%0d", hart);
    lbl_tval_zero = $sformatf("snippy_ill_tval0_h%0d", hart);
    lbl_have_tval = $sformatf("snippy_ill_havetval_h%0d", hart);
    lbl_real0     = $sformatf("snippy_ill_real0_h%0d", hart);


    gen_signature_handshake(instr, CORE_STATUS, ILLEGAL_INSTR_EXCEPTION);
    gen_signature_handshake(.instr(instr), .signature_type(WRITE_CSR), .csr(MCAUSE));

    instr = {instr,
      // r_mepc = mepc
      $sformatf("csrr  x%0d, 0x%0x", r_mepc, MEPC),

      // r_tval = mtval, which can be zero.
      $sformatf("csrr  x%0d, 0x%0x", r_tval, MTVAL),

      // default len=4
      $sformatf("li    x%0d, 4", r_len),

      // If mtval == 0, distinguish real 0x00000000 instruction vs CSR-forced mtval=0
      $sformatf("beqz  x%0d, %s", r_tval, lbl_tval_zero),
      $sformatf("j     %s", lbl_have_tval),

      $sformatf("%s:", lbl_tval_zero),
      // Safe fetch from possibly halfword-aligned mepc: read 2x16b and check if both are zero
      $sformatf("lhu   x%0d, 0(x%0d)", r_tmp, r_mepc),  // low16  -> r_tmp
      $sformatf("lhu   x%0d, 2(x%0d)", r_len, r_mepc),  // high16 -> r_len (used as scratch here)
      $sformatf("or    x%0d, x%0d, x%0d", r_tmp, r_tmp, r_len),
      $sformatf("beqz  x%0d, %s", r_tmp, lbl_real0),

      // CSR-case: rebuild full 32-bit instruction into r_tmp and copy to r_tval
      $sformatf("lhu   x%0d, 0(x%0d)", r_tmp, r_mepc),  // low16
      $sformatf("lhu   x%0d, 2(x%0d)", r_len, r_mepc),  // high16 (scratch)
      $sformatf("slli  x%0d, x%0d, 16", r_len, r_len),
      $sformatf("or    x%0d, x%0d, x%0d", r_tmp, r_tmp, r_len),
      $sformatf("mv    x%0d, x%0d", r_tval, r_tmp),

      // Restore default len=4 and continue with the original length-detection logic
      $sformatf("li    x%0d, 4", r_len),
      $sformatf("j     %s", lbl_have_tval),

      $sformatf("%s:", lbl_real0),
      // Real 0x00000000: keep len=4 and finish
      $sformatf("li    x%0d, 4", r_len),
      $sformatf("j     %s", lbl_done),

      $sformatf("%s:", lbl_have_tval),

      // if (mtval & 3) != 3 -> len=2 (compressed)
      $sformatf("andi  x%0d, x%0d, 3", r_tmp, r_tval),
      $sformatf("li    x%0d, 3", r_len),
      $sformatf("bne   x%0d, x%0d, %s", r_tmp, r_len, lbl_use2),

      // here (mtval & 3) == 3 => 32/48/64
      // check 64-bit prefix: 0111111 (7 bits) => (mtval & 0x7f) == 0x3f
      $sformatf("andi  x%0d, x%0d, 0x7f", r_tmp, r_tval),
      $sformatf("li    x%0d, 0x3f", r_len),
      $sformatf("beq   x%0d, x%0d, %s", r_tmp, r_len, lbl_use8),

      // check 48-bit prefix: 011111 (6 bits) => (mtval & 0x3f) == 0x1f
      $sformatf("andi  x%0d, x%0d, 0x3f", r_tmp, r_tval),
      $sformatf("li    x%0d, 0x1f", r_len),
      $sformatf("beq   x%0d, x%0d, %s", r_tmp, r_len, lbl_use6),

      // otherwise keep 32-bit: len=4
      $sformatf("li    x%0d, 4", r_len),
      $sformatf("j     %s", lbl_done),

      $sformatf("%s:", lbl_use2),
      $sformatf("li    x%0d, 2", r_len),
      $sformatf("j     %s", lbl_done),

      $sformatf("%s:", lbl_use6),
      $sformatf("li    x%0d, 6", r_len),
      $sformatf("j     %s", lbl_done),

      $sformatf("%s:", lbl_use8),
      $sformatf("li    x%0d, 8", r_len),
      $sformatf("j     %s", lbl_done),

      $sformatf("%s:", lbl_done),
      // mepc += len
      $sformatf("add   x%0d, x%0d, x%0d", r_mepc, r_mepc, r_len),
      $sformatf("csrw  0x%0x, x%0d", MEPC, r_mepc)
    };

    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv,
                              cfg.sp, cfg.tp, instr);
    instr.push_back("mret");
    gen_section(get_label("illegal_instr_handler", hart), instr);
  endfunction

endclass
