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
  output logic        ack_o,
  output logic [31:0] rdata_o,

  output logic        instr_req_o,
  output logic [31:0] instr_addr_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  input  logic [31:0] instr_rdata_i,

  output logic [31:0] last_addr_o,

  input  logic        stall_if_i,

  input  logic        drop_request_i
);

  enum logic [2:0] {IDLE, PENDING, WAIT_RVALID, WAIT_IF_STALL, WAIT_GNT, ABORT} CS, NS;

  logic        save_rdata;
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

      if (save_rdata)
        rdata_Q <= instr_rdata_i;
    end
  end


  assign last_addr_o = addr_Q;


  always_comb
  begin
    instr_req_o   = 1'b0;
    ack_o         = 1'b0;
    save_rdata    = 1'b0;
    rdata_o       = instr_rdata_i;
    instr_addr_o  = addr_i;
    wait_gnt      = 1'b0;

    unique case(CS)
      IDLE:
      begin
        instr_req_o = req_i;
        ack_o       = 1'b0;
        rdata_o     = rdata_Q;

        if(req_i)
        begin
          if(instr_gnt_i) //~>  granted request
            NS = PENDING;
          else begin //~> got a request but no grant
            NS       = WAIT_GNT;
            wait_gnt = 1'b1;
          end
        end //~> if(req_i == 0)
        else
        begin
           NS = IDLE;
        end
      end // case: IDLE

      WAIT_GNT:
      begin
        instr_addr_o = addr_Q;
        instr_req_o  = 1'b1;

        if(instr_gnt_i)
          NS = PENDING;
        else
        begin
//        if (drop_request_i)
//          NS = IDLE;
//        else
            NS = WAIT_GNT;
        end
      end // case: WAIT_GNT

      PENDING:
      begin
        if (instr_rvalid_i) begin
          save_rdata = 1'b1;
          ack_o = 1'b1;

          if (stall_if_i) begin
            NS          = WAIT_IF_STALL;
            instr_req_o = 1'b0;
          end else begin
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
          end
        end else begin
          NS          = WAIT_RVALID;
          instr_req_o = 1'b0;
          ack_o       = 1'b0;
        end
      end // case: PENDING

      WAIT_RVALID :
      begin
        NS          = WAIT_RVALID;
        ack_o       = 1'b0;
        instr_req_o = 1'b0;

        if (instr_rvalid_i) begin
          ack_o       = 1'b1;
          save_rdata  = 1'b1;

          if (stall_if_i) begin
            instr_req_o = 1'b0;
            NS          = WAIT_IF_STALL;
          end else begin
            instr_req_o = req_i;
            if (req_i) begin
              if (instr_gnt_i)
                NS =  PENDING;
              else begin
                NS       = WAIT_GNT;
                wait_gnt = 1'b1;
              end
            end else
              NS = IDLE;
          end
        end
      end // case: WAIT_RVALID

      WAIT_IF_STALL:
      begin
        ack_o   = 1'b1;
        rdata_o = rdata_Q;

        if (stall_if_i) begin
          NS          = WAIT_IF_STALL;
          instr_req_o = 1'b0;
        end
        else
        begin
          instr_req_o = req_i;

          if (req_i) begin
            if (instr_gnt_i)
              NS =  PENDING;
            else begin
              NS       = WAIT_GNT;
              wait_gnt = 1'b1;
            end
          end else
            NS = IDLE;
        end
      end // case: WAIT_IF_STALL

      ABORT:
      begin
        NS = IDLE;
        ack_o = 1'b1;
        instr_req_o  = 1'b1;

        if (req_i) begin
          if(instr_gnt_i) //~>  granted request
            NS = PENDING;
          else begin //~> got a request but no grant
            NS       = WAIT_GNT;
            wait_gnt = 1'b1;
          end
        end
      end // case: ABORT

      default:
      begin
        NS          = IDLE;
        instr_req_o = 1'b0;
      end
    endcase
  end

endmodule
