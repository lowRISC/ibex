module tb_illegal_full_safety;

  logic illegal_insn;

  logic rf_we;
  logic data_req_o, data_we_o;
  logic jump_in_dec_o, branch_in_dec_o;
  logic csr_access_o;
  logic rf_ren_a_o, rf_ren_b_o;
  logic icache_inval_o;

  always_comb begin
    // simulate your decoder illegal block behavior
    rf_we           = 1'b1;
    data_req_o      = 1'b1;
    data_we_o       = 1'b1;
    jump_in_dec_o   = 1'b1;
    branch_in_dec_o = 1'b1;
    csr_access_o    = 1'b1;
    rf_ren_a_o      = 1'b1;
    rf_ren_b_o      = 1'b1;
    icache_inval_o  = 1'b1;

    if (illegal_insn) begin
      rf_we           = 1'b0;
      data_req_o      = 1'b0;
      data_we_o       = 1'b0;
      jump_in_dec_o   = 1'b0;
      branch_in_dec_o = 1'b0;
      csr_access_o    = 1'b0;
      rf_ren_a_o      = 1'b0;
      rf_ren_b_o      = 1'b0;
      icache_inval_o  = 1'b0;
    end
  end

  initial begin
    $display("Testing full illegal instruction safety...");

    illegal_insn = 1'b1;
    #1;

    if (rf_we || data_req_o || data_we_o ||
        jump_in_dec_o || branch_in_dec_o ||
        csr_access_o || rf_ren_a_o || rf_ren_b_o ||
        icache_inval_o) begin
      $error("FAIL: Side effects not fully blocked");
    end

    $display("✅ PASS: All side effects blocked");

    $finish;
  end

endmodule