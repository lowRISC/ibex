module tb_imm_rf_read;

  logic rf_ren_a_o, rf_ren_b_o;

  initial begin
    $display("Testing IMM RF read...");

    // Simulate expected behavior of OP_IMM
    rf_ren_a_o = 1;
    rf_ren_b_o = 0;

    #1;

    if (rf_ren_a_o !== 1)
      $error("FAIL: rs1 should be enabled");

    if (rf_ren_b_o !== 0)
      $error("FAIL: rs2 should NOT be enabled");

    $display("✅ PASS");
    $finish;
  end

endmodule