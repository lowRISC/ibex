////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                 DEI @ UNIBO - University of Bologna                        //
//                                                                            //
// Engineer:       Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Create Date:    08/08/2014                                                 //
// Design Name:    hwloop regs                                                //
// Module Name:    hwloop_regs.sv                                             //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Hardware loop registers                                    //
//                 a) store start/end address of N=4 hardware loops           //
//                 b) store init value of counter for each hardware loop      //
//                 c) decrement counter if hwloop taken                       //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "defines.sv"

module hwloop_regs
(
  input  logic        clk,
  input  logic        rst_n,

  // from ex stage
  input  logic [31:0] hwloop_start_data_i,
  input  logic [31:0] hwloop_end_data_i,
  input  logic [31:0] hwloop_cnt_data_i,
  input  logic  [2:0] hwloop_we_i,
  input  logic  [1:0] hwloop_regid_i,         // selects the register set

  // from controller
  input  logic        stall_id_i,

  // from hwloop controller
  input  logic [`HWLOOP_REGS-1:0]        hwloop_dec_cnt_i,

  // to hwloop controller
  output logic [`HWLOOP_REGS-1:0] [31:0] hwloop_start_addr_o,
  output logic [`HWLOOP_REGS-1:0] [31:0] hwloop_end_addr_o,
  output logic [`HWLOOP_REGS-1:0] [31:0] hwloop_counter_o
);


  logic [`HWLOOP_REGS-1:0] [31:0] hwloop_start_regs_q;
  logic [`HWLOOP_REGS-1:0] [31:0] hwloop_end_regs_q;
  logic [`HWLOOP_REGS-1:0] [31:0] hwloop_counter_regs_q;

  int unsigned i;


  assign hwloop_start_addr_o = hwloop_start_regs_q;
  assign hwloop_end_addr_o   = hwloop_end_regs_q;
  assign hwloop_counter_o    = hwloop_counter_regs_q;


  /////////////////////////////////////////////////////////////////////////////////
  // HWLOOP start-address register                                               //
  /////////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : HWLOOP_REGS_START
    if (rst_n == 1'b0)
    begin
      for(i=0; i<`HWLOOP_REGS; i++) begin
        hwloop_start_regs_q[i] <= 32'h0000_0000;
      end
    end
    else if (hwloop_we_i[0] == 1'b1)
    begin
      hwloop_start_regs_q[hwloop_regid_i] <= hwloop_start_data_i;
    end
  end


  /////////////////////////////////////////////////////////////////////////////////
  // HWLOOP end-address register                                                 //
  /////////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : HWLOOP_REGS_END
    if (rst_n == 1'b0)
    begin
      for(i=0; i<`HWLOOP_REGS; i++) begin
        hwloop_end_regs_q[i] <= 32'h0000_0000;
      end
    end
    else if (hwloop_we_i[1] == 1'b1)
    begin
      hwloop_end_regs_q[hwloop_regid_i] <= hwloop_end_data_i;
    end
  end


  /////////////////////////////////////////////////////////////////////////////////
  // HWLOOP counter register with decrement logic                                //
  /////////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : HWLOOP_REGS_COUNTER
    if (rst_n == 1'b0)
    begin
      for (i=0; i<`HWLOOP_REGS; i++) begin
        hwloop_counter_regs_q[i] <= 32'h0000_0000;
      end
    end
    else if (hwloop_we_i[2] == 1'b1) // potential contention problem here!
    begin
      hwloop_counter_regs_q[hwloop_regid_i] <= hwloop_cnt_data_i;
    end
    else
    begin
      for (i=0; i<`HWLOOP_REGS; i++)
      begin
        if ((hwloop_dec_cnt_i[i] == 1'b1) && (stall_id_i == 1'b0))
          hwloop_counter_regs_q[i] <= hwloop_counter_regs_q[i] - 1;
      end
    end
  end

endmodule
