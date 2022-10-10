// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


// Define a short riscv-dv directed instruction stream to setup hardware breakpoints
// (TSELECT/TDATA), and then trigger on an instruction at the end of this stream.
class ibex_breakpoint_stream extends riscv_directed_instr_stream;

  riscv_pseudo_instr   la_instr;
  riscv_instr          ebreak_insn;
  rand int unsigned    num_of_instr;

  constraint instr_c {
    num_of_instr inside {[5:10]};
  }

  `uvm_object_utils(ibex_breakpoint_stream)

  function new(string name = "");
    super.new(name);
  endfunction

  function void post_randomize();
    riscv_instr      instr;
    string           trigger_label, gn;

    // Setup a randomized main body of instructions.
    initialize_instr_list(num_of_instr);
    setup_allowed_instr(1, 1); // no_branch=1/no_load_store=1
    foreach(instr_list[i]) begin
      instr = riscv_instr::type_id::create("instr");
      randomize_instr(instr);
      instr_list[i] = instr;
      // Copy this from the base-class behaviour
      instr_list[i].atomic = 1'b1;
      instr_list[i].has_label = 1'b0;
    end

    // Give the last insn of the main body a label, then set the breakpoint address to that label.
    gn = get_name();
    trigger_label = {gn};
    instr_list[$].label = trigger_label;
    instr_list[$].has_label = 1'b1;

    // Load the address of the trigger point as the (last insn of the stream + 4)
    // Store in gpr[1] ()
    la_instr = riscv_pseudo_instr::type_id::create("la_instr");
    la_instr.pseudo_instr_name = LA;
    la_instr.imm_str           = $sformatf("%0s+4", trigger_label);
    la_instr.rd                = cfg.gpr[1];

    // Create the ebreak insn which will cause us to enter debug mode, and run the
    // special code in the debugrom.
    ebreak_insn = riscv_instr::get_instr(EBREAK);

    // Add the instructions into the stream.
    instr_list = {la_instr,
                  ebreak_insn,
                  instr_list};
  endfunction

endclass
