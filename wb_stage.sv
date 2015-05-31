////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                 DEI @ UNIBO - University of Bologna                        //
//                                                                            //
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
//                                                                            //
// Create Date:    01/07/2014                                                 //
// Design Name:    Write Back stage                                           //
// Module Name:    wb_stage.sv                                                //
// Project Name:   OR10N                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Execution stage: hosts a Multiplexer that select data to   //
//                 write in the register file (from data interface or SP reg  //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (August 6th 2014) Changed port and signal names, addedd    //
//                 comments                                                   //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
// sp = special register
// id = instruction decode
// if = instruction fetch
// ex = execute stage
// wb = write back
// data = from data memory


`include "defines.sv"

module wb_stage
(
    // MUX SELECTOR --> Used to select what write in the register file
    input  logic        regfile_wdata_mux_sel_i,  // Comes from the controller (thru id-ex and ex-wb pipe)

    // MUX INPUTS
    input  logic [31:0] data_rdata_i,            // read Data from data memory system
    input  logic [31:0] lsu_data_reg_i,          // TODO: remove; read data registered in LSU
    // MUX OUTPUT
    output logic [31:0] regfile_wdata_o         // write data for register file

);

   // TODO: Remove this mux and the associated signals
   // Register Write Data Selection --> Data to write in the regfile
   // Select between:
   // 0:    From Special Register
   // 1:    From Data Memory
   always_comb
   begin : REGFILE_WDATA_MUX
      casex (regfile_wdata_mux_sel_i)
        //1'b0:  begin regfile_wdata_o <= sp_rdata_i;        end
        1'b1:  begin regfile_wdata_o <= data_rdata_i;      end
      endcase; // case (regfile_wdata_mux_sel_i)
   end

endmodule
