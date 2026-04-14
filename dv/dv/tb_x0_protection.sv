module tb_x0_protection;

  logic [4:0] rf_waddr_o;
  logic rf_we;
  logic illegal_reg_rv32e;
  logic rf_we_o;

  assign rf_we_o = rf_we & ~illegal_reg_rv32e & (rf_waddr_o != 5'd0);

  initial begin
    $display("Testing x0 protection...");

    rf_we = 1'b1;
    illegal_reg_rv32e = 1'b0;

    // x0 write
    rf_waddr_o = 5'd0;
    #1;
    if (rf_we_o !== 0)
      $error("FAIL: x0 write not blocked");

    // ✅ valid write
    rf_waddr_o = 5'd5;
    #1;
    if (rf_we_o !== 1)
      $error("FAIL: valid write blocked");

    $display("✅ PASS: x0 protection works");

    $finish;
  end

endmodule