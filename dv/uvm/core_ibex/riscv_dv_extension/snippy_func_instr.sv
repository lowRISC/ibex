class snippy_func_instr extends riscv_instr_sequence;
  `uvm_object_utils(snippy_func_instr)

  function new(string name = "");
    super.new(name);
  endfunction
  
  typedef string string_q_t[$];

  function automatic string_q_t gen_stack_ops(string op, const ref string regs[]);
    string_q_t result = {};
    int unsigned n = regs.size();
    int unsigned max_of = (n==0) ? 0 : (n-1)*4;
    foreach (regs[i]) begin
      int unsigned off = max_of - i*4;
      result.push_back($sformatf("                  %s %s, %0d(sp)", op, regs[i], off));
    end
    return result;
  endfunction

  virtual function void generate_instr_stream(bit no_label = 1'b0);
    // list of all saved registers (callee‑saved + caller‑saved)
    string saved_regs[] = '{"s0","s1","s2","s3","s4","s5",
                            "s6","s7","s8","s9","s10","s11",
                            "ra","tp","gp",
                            "t0","t1","t2","t3","t4","t5","t6",
                            "a0","a1","a2","a3","a4","a5","a6","a7"};
    instr_string_list = {};

    // global variable for saving sp
    instr_string_list.push_back("                  .section .data");
    instr_string_list.push_back("                  .align 2");
    instr_string_list.push_back("saved_sp:");
    instr_string_list.push_back("                  .word 0");

    // code
    instr_string_list.push_back("                  .section .text");
    instr_string_list.push_back("main:");

    instr_string_list.push_back("                  addi sp, sp, -128");

    instr_string_list = {instr_string_list, gen_stack_ops("sw", saved_regs)};

    // save current stack pointer in global
    instr_string_list.push_back("                  la t0, saved_sp");
    instr_string_list.push_back("                  sw sp, 0(t0)");

    instr_string_list.push_back("                  call SnippyFunction");

    // restore sp
    instr_string_list.push_back("                  la t0, saved_sp");
    instr_string_list.push_back("                  lw sp, 0(t0)");

    instr_string_list = {instr_string_list, gen_stack_ops("lw", saved_regs)};

    instr_string_list.push_back("                  addi sp, sp, 128");
  endfunction

endclass
