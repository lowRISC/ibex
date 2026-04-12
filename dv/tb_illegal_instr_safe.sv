`timescale 1ns/1ps

module tb_illegal_instr_safe;

  logic clk;
  logic rst_n;

  logic [31:0] instr_rdata_i;
  logic [31:0] instr_rdata_alu_i;

  logic rf_we_o;
  logic data_req_o;
  logic jump_in_dec_o;

  // clock
  always #5 clk = ~clk;

  ibex_decoder dut (
    .clk_i(clk),
    .rst_ni(rst_n),

    .instr_rdata_i(instr_rdata_i),
    .instr_rdata_alu_i(instr_rdata_alu_i),

    .rf_we_o(rf_we_o),
    .data_req_o(data_req_o),
    .jump_in_dec_o(jump_in_dec_o)
  );

  initial begin
    clk = 0;
    rst_n = 0;
    #10 rst_n = 1;

    // Inject illegal instruction
    instr_rdata_i     = 32'hFFFFFFFF;
    instr_rdata_alu_i = 32'hFFFFFFFF;

    #10;

    // Checks
    if (rf_we_o !== 0) $fatal("FAIL: rf_we_o not zero");
    if (data_req_o !== 0) $fatal("FAIL: data_req_o not zero");
    if (jump_in_dec_o !== 0) $fatal("FAIL: jump not zero");

    $display("PASS: Illegal instruction handled safely");
    $finish;
  end

endmodule