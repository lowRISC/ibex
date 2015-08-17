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
// Project Name:   RI5CY                                                      //
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
    // MUX INPUTS
    input  logic [31:0] data_rdata_i,            // read Data from data memory system

    // MUX OUTPUT
    output logic [31:0] regfile_wdata_o         // write data for register file

);

 assign regfile_wdata_o = data_rdata_i;

endmodule
