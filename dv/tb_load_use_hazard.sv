module tb_load_use_hazard;

  logic clk;
  logic rst_n;

  // Inputs
  logic [31:0] instr;
  logic illegal_c_insn_i;

  // Outputs
  logic rf_we_o;

  // Instantiate DUT (adjust if needed)
  ibex_decoder dut (
    .instr_i(instr),
    .illegal_c_insn_i(illegal_c_insn_i),
    .rf_we_o(rf_we_o)
  );

  // Clock
  always #5 clk = ~clk;

  initial begin
    clk = 0;
    rst_n = 0;
    illegal_c_insn_i = 0;

    #10 rst_n = 1;

    //Simulate load instruction
    instr = 32'h00002083; // lw x1, 0(x0)
    #10;

    //Dependent instruction (uses x1)
    instr = 32'h001080B3; // add x1, x1, x1
    #10;

    // Check
    if (rf_we_o == 0)
      $display("PASS: Load-use hazard blocked write");
    else
      $display("FAIL: Hazard not handled");

    $finish;
  end

endmodule