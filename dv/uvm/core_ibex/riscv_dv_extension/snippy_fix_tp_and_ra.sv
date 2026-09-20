class ibex_riscv_instr_gen_config extends riscv_instr_gen_config;
  `uvm_object_utils(ibex_riscv_instr_gen_config)

  constraint ibex_fix_tp_and_ra_c {
    tp == TP;
    ra == RA;
  }

  function new(string name = "");
    super.new(name);
  endfunction
endclass
