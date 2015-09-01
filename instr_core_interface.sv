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

  enum logic [1:0] {IDLE, PENDING, WAIT_RVALID, WAIT_GNT } CS, NS;

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

      if (instr_req_o && instr_gnt_i)
        addr_Q <= instr_addr_o;

      if (wait_gnt)
        addr_Q <= addr_i;

      if (instr_rvalid_i)
        rdata_Q <= instr_rdata_i;
    end
  end

  assign valid_o      = instr_rvalid_i;

  always_comb
  begin
    instr_req_o   = 1'b0;
    rdata_o       = instr_rdata_i;
    instr_addr_o  = addr_i;
    wait_gnt      = 1'b0;

    unique case(CS)
      // default state, not waiting for requested data
      IDLE:
      begin
        rdata_o     = rdata_Q;

        NS          = IDLE;
        instr_req_o = req_i;

        if(req_i) begin
          if(instr_gnt_i) //~>  granted request
            NS = PENDING;
          else begin //~> got a request but no grant
            NS       = WAIT_GNT;
            wait_gnt = 1'b1;
          end
        end
      end // case: IDLE

      // we sent a request but did not yet get a grant
      WAIT_GNT:
      begin
        instr_addr_o = addr_Q;
        instr_req_o  = 1'b1;

        if(instr_gnt_i)
          NS = PENDING;
        else
        begin
          NS = WAIT_GNT;
        end
      end // case: WAIT_GNT

      // we got a grant, so now we wait for the rvalid
      PENDING:
      begin
        if (instr_rvalid_i) begin
          NS          = IDLE;
          instr_req_o = req_i;

          if (req_i) begin
            if (instr_gnt_i) begin
              NS = PENDING;
            end else begin
              NS       = WAIT_GNT;
              wait_gnt = 1'b1;
            end
          end
        end else begin
          NS          = WAIT_RVALID;
          instr_req_o = 1'b0;
        end
      end // case: PENDING

      // we wait for rvalid, after that we are ready to serve a new request
      WAIT_RVALID :
      begin
        NS          = WAIT_RVALID;
        instr_req_o = 1'b0;

        if (instr_rvalid_i) begin
          NS          = IDLE;
          instr_req_o = req_i;

          if (req_i) begin
            if (instr_gnt_i)
              NS =  PENDING;
            else begin
              NS       = WAIT_GNT;
              wait_gnt = 1'b1;
            end
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
