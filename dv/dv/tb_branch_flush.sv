`timescale 1ns/1ps

module tb_branch_flush;

  logic clk;
  logic rst_n;

  logic branch_taken_i;
  logic [31:0] instr_rdata_i;
  logic [31:0] instr_rdata_alu_i;

  logic data_req_o;
  logic data_we_o;

  always #5 clk = ~clk;

  ibex_decoder dut (
    .clk_i(clk),
    .rst_ni(rst_n),
    .branch_taken_i(branch_taken_i),
    .instr_rdata_i(instr_rdata_i),
    .instr_rdata_alu_i(instr_rdata_alu_i),
    .data_req_o(data_req_o),
    .data_we_o(data_we_o)
  );

  initial begin
    clk = 0;
    rst_n = 0;
    branch_taken_i = 0;

    #10 rst_n = 1;

    // Simulate branch instruction
    instr_rdata_i     = 32'h00000063; // BEQ type
    instr_rdata_alu_i = 32'h00000063;

    branch_taken_i = 1;

    #10;

    // Check memory is blocked
    if (data_req_o !== 0) $fatal("FAIL: data_req_o should be 0 on branch");
    if (data_we_o  !== 0) $fatal("FAIL: data_we_o should be 0 on branch");

    $display("PASS: Branch flush safe");
    $finish;
  end

endmodule