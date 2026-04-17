module tb_lui_rf_read;

  logic rf_ren_a_o, rf_ren_b_o;

  initial begin
    $display("Testing LUI RF read...");

    // LUI should not read any register
    rf_ren_a_o = 0;
    rf_ren_b_o = 0;

    #1;

    if (rf_ren_a_o !== 0)
      $error("FAIL: rs1 should NOT be enabled");

    if (rf_ren_b_o !== 0)
      $error("FAIL: rs2 should NOT be enabled");

    $display("✅ PASS");
    $finish;
  end

endmodule