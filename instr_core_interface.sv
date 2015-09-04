////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                 DEI @ UNIBO - University of Bologna                        //
//                                                                            //
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Create Date:    06/08/2014                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    instr_core_interface.sv                                    //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction Fetch interface used to properly handle        //
//                 cache stalls                                               //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module instr_core_interface
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        req_i,
  input  logic [31:0] addr_i,
  output logic        valid_o,
  output logic [31:0] rdata_o,
  output logic [31:0] last_addr_o,

  output logic        instr_req_o,
  output logic [31:0] instr_addr_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  input  logic [31:0] instr_rdata_i
);

  enum logic [1:0] {IDLE, WAIT_RVALID, WAIT_GNT } CS, NS;

  logic [31:0] rdata_Q;

  logic        wait_gnt;
  logic [31:0] addr_Q;

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      CS      <= IDLE;
      rdata_Q <= '0;
      addr_Q  <= '0;
    end
    else
    begin
      CS <= NS;

      if (wait_gnt)
        addr_Q <= instr_addr_o;

      if (instr_rvalid_i)
        rdata_Q <= instr_rdata_i;
    end
  end

  assign valid_o      = instr_rvalid_i;
  assign last_addr_o  = addr_Q;

  always_comb
  begin
    instr_req_o   = 1'b0;
    rdata_o       = instr_rdata_i;
    instr_addr_o  = addr_i;
    wait_gnt      = 1'b0;
    NS            = CS;

    unique case(CS)
      // default state, not waiting for requested data
      IDLE:
      begin
        rdata_o     = rdata_Q;

        instr_req_o = 1'b0;

        if(req_i) begin
          instr_req_o = 1'b1;

          wait_gnt = 1'b1;
          if(instr_gnt_i) //~>  granted request
            NS       = WAIT_RVALID;
          else begin //~> got a request but no grant
            NS       = WAIT_GNT;
          end
        end
      end // case: IDLE

      // we sent a request but did not yet get a grant
      WAIT_GNT:
      begin
        instr_addr_o = addr_Q;
        instr_req_o  = 1'b1;

        if(instr_gnt_i)
          NS = WAIT_RVALID;
        else
          NS = WAIT_GNT;
      end // case: WAIT_GNT

      // we wait for rvalid, after that we are ready to serve a new request
      WAIT_RVALID :
      begin

        if (req_i) begin
          // prepare for next request
          instr_req_o = 1'b1;

          if (instr_rvalid_i) begin
            wait_gnt = 1'b1;
            if (instr_gnt_i) begin
              NS      = WAIT_RVALID;
            end else begin
              NS      = WAIT_GNT;
            end
          end
        end else begin
          // just wait for rvalid and go back to IDLE, no new request
          // requested
          instr_req_o = 1'b0;

          if (instr_rvalid_i) begin
            NS = IDLE;
          end
        end
      end // case: WAIT_RVALID

      default:
      begin
        NS          = IDLE;
        instr_req_o = 1'b0;
      end
    endcase
  end

endmodule
