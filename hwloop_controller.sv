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
// Design Name:    hwloop controller                                          //
// Module Name:    hwloop_controller.sv                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Hardware loop controller unit. This unit is responsible to //
//                 handle hardware loops. Tasks are:                          //
//                 a) compare PC to all stored end addresses                  //
//                 b) jump to the right start address if counter =/ 0         //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "defines.sv"

module riscv_hwloop_controller
#(
  parameter N_REGS = 2
)
(
  // from id stage
  input  logic [31:0]              current_pc_i,

  // from hwloop_regs
  input  logic [N_REGS-1:0] [31:0] hwlp_start_addr_i,
  input  logic [N_REGS-1:0] [31:0] hwlp_end_addr_i,
  input  logic [N_REGS-1:0] [31:0] hwlp_counter_i,

  // to hwloop_regs
  output logic [N_REGS-1:0]        hwlp_dec_cnt_o,

  // from pipeline stages
  input  logic [N_REGS-1:0]        hwlp_dec_cnt_id_i,

  // to id stage
  output logic                     hwlp_jump_o,
  output logic [31:0]              hwlp_targ_addr_o
);


  logic [N_REGS-1:0] pc_is_end_addr;

  // end address detection
  integer j;


  // generate comparators. check for end address and the loop counter
  genvar i;
  generate
    for (i = 0; i < N_REGS; i++) begin
      always @(*)
      begin
        pc_is_end_addr[i] = 1'b0;

        if (current_pc_i == hwlp_end_addr_i[i]) begin
          if (hwlp_counter_i[i][31:2] != 30'h0) begin
            pc_is_end_addr[i] = 1'b1;
          end else begin
            // hwlp_counter_i[i][31:2] == 32'h0
            case (hwlp_counter_i[i][1:0])
              2'b11:        pc_is_end_addr[i] = 1'b1;
              2'b10:        pc_is_end_addr[i] = ~hwlp_dec_cnt_id_i[i]; // only when there is nothing in flight
              2'b01, 2'b00: pc_is_end_addr[i] = 1'b0;
            endcase
          end
        end
      end
    end
  endgenerate

  // select corresponding start address and decrement counter
  always_comb
  begin
    hwlp_targ_addr_o = 'x;
    hwlp_dec_cnt_o   = '0;

    for (j = 0; j < N_REGS; j++) begin
      if (pc_is_end_addr[j]) begin
        hwlp_targ_addr_o  = hwlp_start_addr_i[j];
        hwlp_dec_cnt_o[j] = 1'b1;
        break;
      end
    end
  end

  // output signal for ID stage
  assign hwlp_jump_o = (|pc_is_end_addr);

endmodule
