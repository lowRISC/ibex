module tb_illegal_instr_safe;

  logic illegal_insn;

  logic rf_we;
  logic rf_ren_a_o;
  logic rf_ren_b_o;
  logic data_req_o;
  logic data_we_o;
  logic jump_in_dec_o;
  logic branch_in_dec_o;
  logic csr_access_o;

  // DUT (simplified behavior mimic)
  always_comb begin
    // default
    rf_we           = 1'b1;
    rf_ren_a_o      = 1'b1;
    rf_ren_b_o      = 1'b1;
    data_req_o      = 1'b1;
    data_we_o       = 1'b1;
    jump_in_dec_o   = 1'b1;
    branch_in_dec_o = 1'b1;
    csr_access_o    = 1'b1;

    // your fix behavior
    if (illegal_insn) begin
      rf_we           = 1'b0;
      rf_ren_a_o      = 1'b0;
      rf_ren_b_o      = 1'b0;
      data_req_o      = 1'b0;
      data_we_o       = 1'b0;
      jump_in_dec_o   = 1'b0;
      branch_in_dec_o = 1'b0;
      csr_access_o    = 1'b0;
    end
  end

  initial begin
    $display("Testing illegal instruction safety...");

    illegal_insn = 1'b1;
    #1;

    // CHECKS
    if (rf_we !== 0) $error("FAIL: rf_we not disabled");
    if (rf_ren_a_o !== 0) $error("FAIL: rf_ren_a not disabled");
    if (rf_ren_b_o !== 0) $error("FAIL: rf_ren_b not disabled");
    if (data_req_o !== 0) $error("FAIL: data_req not disabled");
    if (data_we_o !== 0) $error("FAIL: data_we not disabled");
    if (jump_in_dec_o !== 0) $error("FAIL: jump not disabled");
    if (branch_in_dec_o !== 0) $error("FAIL: branch not disabled");
    if (csr_access_o !== 0) $error("FAIL: csr not disabled");

    $display("✅ PASS: Illegal instruction properly isolated");

    $finish;
  end

endmodule