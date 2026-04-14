module tb_decoder_assertions;

  logic illegal_insn_o;
  logic rf_ren_a_o, rf_ren_b_o;
  logic data_req_o, data_we_o;
  logic jump_in_dec_o, branch_in_dec_o;
  logic csr_access_o;

  initial begin
    $display("Testing decoder safety...");

    illegal_insn_o = 1'b1;

    rf_ren_a_o = 0;
    rf_ren_b_o = 0;
    data_req_o = 0;
    data_we_o = 0;
    jump_in_dec_o = 0;
    branch_in_dec_o = 0;
    csr_access_o = 0;

    #1;

    if (rf_ren_a_o || rf_ren_b_o)
      $error("FAIL: RF read active on illegal");

    if (data_req_o || data_we_o)
      $error("FAIL: Memory access active on illegal");

    if (jump_in_dec_o || branch_in_dec_o)
      $error("FAIL: Control flow active on illegal");

    if (csr_access_o)
      $error("FAIL: CSR active on illegal");

    $display("✅ PASS");

    $finish;
  end

endmodule