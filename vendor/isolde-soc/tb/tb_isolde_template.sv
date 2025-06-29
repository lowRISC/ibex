`timescale 1ns/1ps

module tb_isolde_template(
    input logic clk_i,
    input logic rst_ni,
    input logic fetch_enable_i

);



logic [7:0] d = 0;
logic [7:0] q = 0;

// Input signal generation
//https://github.com/verilator/verilator/issues/5210
//*
//if you need <= assignment in initial block, change the block into allways, otherways it will be treated as =, blocking assigment.
//*
//initial begin
always begin
    do @(posedge clk_i); while (!fetch_enable_i);
    d <= 0;
    repeat (5) @(posedge clk_i);
    d <= 1;
    @(posedge clk_i);
    d <= 2;
    @(posedge clk_i);
    d <= 3;
    @(posedge clk_i);
    d <= 4;
    @(posedge clk_i);
    d <= 0;
    repeat (5) @(posedge clk_i);
    $finish;
end

// Unit under test (flip-flop)
always @(posedge clk_i)
    q <= d;

endmodule
