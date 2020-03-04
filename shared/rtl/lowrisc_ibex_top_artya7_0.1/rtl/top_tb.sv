`timescale 1ns/1ps

module top_tb;

   logic               IO_CLK;
   logic               IO_RST_N;
   logic [3:0]         LED;
   // JTAG interface
   logic               jtag_tck_i;
   logic               jtag_tms_i;
   logic               jtag_trst_ni;
   logic               jtag_td_i;
   logic               jtag_td_o;

top_artya7 dut(
.IO_CLK,
.IO_RST_N,
.LED,
.jtag_tck_i,
.jtag_tms_i,
.jtag_trst_ni,
.jtag_td_i,
.jtag_td_o
);

   initial
     begin
        IO_CLK = 0;
        IO_RST_N = 0;
        jtag_tck_i = 0;
        jtag_tms_i = 0;
        jtag_trst_ni = 0;
        jtag_td_i = 0;
        forever
          begin
             #5 IO_CLK = 1;
             #5 IO_CLK = 0;
             #5 IO_CLK = 1;
             #5 IO_CLK = 0;
             #5 IO_CLK = 1;
             #5 IO_CLK = 0;
             #5 IO_CLK = 1;
             #5 IO_CLK = 0;
             #5 IO_CLK = 1;
             #5 IO_CLK = 0;
             IO_RST_N = 1;
             jtag_trst_ni = 1;
          end
     end
      
  initial
      #1000 force dut.debug_req = 1;
        
endmodule // top_tb
