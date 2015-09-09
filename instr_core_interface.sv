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

// input port: send address one cycle before the data
// clear_i clears the FIFO for the following cycle. in_addr_i can be sent in
// this cycle already
module fetch_fifo
(
    input  logic        clk,
    input  logic        rst_n,

    // control signals
    input  logic        clear_i,          // clears the contents of the fifo

    // input port
    input  logic        in_addr_valid_i,
    output logic        in_addr_ready_o,
    input  logic [31:0] in_addr_i,
    output logic [31:0] in_last_addr_o,

    input  logic        in_rdata_valid_i,
    output logic        in_rdata_ready_o,
    input  logic [31:0] in_rdata_i,

    // output port
    output logic        out_valid_o,
    input  logic        out_ready_i,
    output logic [31:0] out_rdata_o,
    output logic [31:0] out_addr_o,

    output logic        out_unaligned_valid_o,
    output logic [31:0] out_unaligned_rdata_o
  );

  localparam DEPTH = 2; // must be 2 or greater

  // index 0 is used for output
  logic [0:DEPTH-1] [31:0]  addr_n,        addr_int,        addr_Q;
  logic [0:DEPTH-1]         addr_valid_n,  addr_valid_int,  addr_valid_Q;
  logic [0:DEPTH-1] [31:0]  rdata_n,       rdata_int,       rdata_Q;
  logic [0:DEPTH-1]         rdata_valid_n, rdata_valid_int, rdata_valid_Q;

  //////////////////////////////////////////////////////////////////////////////
  // output port
  //////////////////////////////////////////////////////////////////////////////

  // output assignments
  assign out_rdata_o = (rdata_valid_Q[0]) ? rdata_Q[0] : in_rdata_i;
  assign out_addr_o  = addr_Q[0]; // always output addr directly since we sent it one cycle earlier to the FIFO

  assign out_valid_o = (rdata_valid_Q[0] || (addr_valid_Q[0] && in_rdata_valid_i));

  assign out_unaligned_rdata_o = (rdata_valid_Q[1]) ? {rdata_Q[1][15:0], out_rdata_o[31:16]} : {in_rdata_i[15:0], out_rdata_o[31:16]};
  // it is implied that rdata_valid_Q[0] is set
  assign out_unaligned_valid_o = (rdata_valid_Q[1] || (addr_valid_Q[1] && in_rdata_valid_i));



  //////////////////////////////////////////////////////////////////////////////
  // input port
  //////////////////////////////////////////////////////////////////////////////

  // we accept addresses as long as our fifo is not full or we are cleared
  assign in_addr_ready_o = clear_i || (~addr_valid_Q[DEPTH-1]);

  // we accept data as long as our fifo is not full
  // we don't care about clear here as the data will be received one cycle
  // later anyway
  assign in_rdata_ready_o = ~rdata_valid_Q[DEPTH-1];


  // output the latest valid address we got
  int i;
  always_comb
  begin
    in_last_addr_o = addr_Q[0];

    for(i = 1; i < DEPTH; i++) begin
      if (addr_valid_Q[i])
        in_last_addr_o = addr_Q[i];
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // FIFO management
  //////////////////////////////////////////////////////////////////////////////

  int j;
  always_comb
  begin
    addr_int        = addr_Q;
    addr_valid_int  = addr_valid_Q;

    if (in_addr_valid_i && in_addr_ready_o) begin
      for(j = 0; j < DEPTH; j++) begin
        if (~addr_valid_Q[j]) begin
          addr_int[j]       = in_addr_i;
          addr_valid_int[j] = 1'b1;

          break;
        end
      end
    end
  end

  int k;
  always_comb
  begin
    rdata_int       = rdata_Q;
    rdata_valid_int = rdata_valid_Q;

    if (in_rdata_valid_i && in_rdata_ready_o) begin
      for(k = 0; k < DEPTH; k++) begin
        if (~rdata_valid_Q[k]) begin
          rdata_int[k]       = in_rdata_i;
          rdata_valid_int[k] = 1'b1;

          break;
        end
      end
    end
  end

  // move everything by one step
  always_comb
  begin
    addr_n        = addr_int;
    addr_valid_n  = addr_valid_int;
    rdata_n       = rdata_int;
    rdata_valid_n = rdata_valid_int;

    if (out_ready_i && out_valid_o) begin
      addr_n        = {addr_int[1:DEPTH-1],       32'b0};
      addr_valid_n  = {addr_valid_int[1:DEPTH-1],  1'b0};
      rdata_n       = {rdata_int[1:DEPTH-1],      32'b0};
      rdata_valid_n = {rdata_valid_int[1:DEPTH-1], 1'b0};
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      addr_Q        <= '{default: '0};
      addr_valid_Q  <= '0;
      rdata_Q       <= '{default: '0};
      rdata_valid_Q <= '0;
    end
    else
    begin
      // on a clear signal from outside we invalidate the content of the FIFO
      // completely and start from an empty state
      if (clear_i) begin
        addr_Q[0]     <= in_addr_i;
        addr_valid_Q  <= {in_addr_valid_i, {DEPTH-1{1'b0}}};
        rdata_valid_Q <= '0;
      end else begin
        addr_Q        <= addr_n;
        addr_valid_Q  <= addr_valid_n;
        rdata_Q       <= rdata_n;
        rdata_valid_Q <= rdata_valid_n;
      end
    end
  end

endmodule

// clear_i deletes everything up to now, i.e. it assumes that addr_i now has
// the correct state and uses the current cycle's addr_i to fetch new data
module instr_core_interface
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        req_i,
  input  logic        clear_i,
  input  logic        ready_i,
  input  logic [31:0] addr_i,

  output logic        valid_o,
  output logic [31:0] rdata_o,
  output logic [31:0] addr_o,

  output logic        unaligned_valid_o,
  output logic [31:0] unaligned_rdata_o,

  // goes to instruction memory / instruction cache
  output logic        instr_req_o,
  output logic [31:0] instr_addr_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  input  logic [31:0] instr_rdata_i
);

  // TODO: THERE IS A PROBLEM WIHT REQ_I AND CLEAR_I
  // i.e. what happens if req_i is low and clear_i is high? the core will miss
  // the updated address....

  enum logic [1:0] {IDLE, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED } CS, NS;

  logic [31:0] addr_next;

  logic        fifo_addr_valid;
  logic        fifo_addr_ready;
  logic [31:0] fifo_last_addr;

  logic        fifo_rdata_valid;
  logic        fifo_rdata_ready;


  //////////////////////////////////////////////////////////////////////////////
  // address selection and increase
  //////////////////////////////////////////////////////////////////////////////

  assign addr_next = (clear_i) ? addr_i : (fifo_last_addr + 32'd4);


  //////////////////////////////////////////////////////////////////////////////
  // fetch fifo
  // consumes addresses and rdata
  //////////////////////////////////////////////////////////////////////////////

  fetch_fifo fifo_i
  (
    .clk                   ( clk               ),
    .rst_n                 ( rst_n             ),

    .clear_i               ( clear_i           ),

    .in_addr_valid_i       ( fifo_addr_valid   ),
    .in_addr_ready_o       ( fifo_addr_ready   ),
    .in_addr_i             ( addr_next         ),
    .in_last_addr_o        ( fifo_last_addr    ),

    .in_rdata_valid_i      ( fifo_rdata_valid  ),
    .in_rdata_ready_o      ( fifo_rdata_ready  ),
    .in_rdata_i            ( instr_rdata_i     ),

    .out_valid_o           ( valid_o           ),
    .out_ready_i           ( ready_i           ),
    .out_rdata_o           ( rdata_o           ),
    .out_addr_o            ( addr_o            ),

    .out_unaligned_valid_o ( unaligned_valid_o ),
    .out_unaligned_rdata_o ( unaligned_rdata_o )
  );


  //////////////////////////////////////////////////////////////////////////////
  // instruction fetch FSM
  // deals with instruction memory / instruction cache
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    instr_req_o      = 1'b0;
    instr_addr_o     = addr_next;
    fifo_addr_valid  = 1'b0;
    fifo_rdata_valid = 1'b0;
    NS               = CS;

    unique case(CS)
      // default state, not waiting for requested data
      IDLE:
      begin
        instr_req_o = 1'b0;

        if (req_i && fifo_addr_ready) begin
          instr_req_o = 1'b1;

          fifo_addr_valid = 1'b1;

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

        if (clear_i) begin
          instr_addr_o = addr_next;

          if (req_i && fifo_addr_ready) begin
            instr_req_o = 1'b1;

            fifo_addr_valid = 1'b1;

            if(instr_gnt_i) //~>  granted request
              NS = WAIT_ABORTED;
            else begin //~> got a request but no grant
              NS = WAIT_GNT;
            end
          end else begin
            if(instr_gnt_i) //~>  granted request
              NS = WAIT_ABORTED;
            else begin //~> got a request but no grant
              NS = IDLE;
            end
          end

        end else begin
          instr_req_o  = 1'b1;
          instr_addr_o = fifo_last_addr;

          if(instr_gnt_i)
            NS = WAIT_RVALID;
          else
            NS = WAIT_GNT;
        end
      end // case: WAIT_GNT

      // we wait for rvalid, after that we are ready to serve a new request
      WAIT_RVALID: begin

        if (req_i && fifo_addr_ready) begin
          // prepare for next request
          instr_req_o = 1'b1;

          if (instr_rvalid_i) begin
            fifo_rdata_valid = 1'b1;
            fifo_addr_valid  = 1'b1;

            if (instr_gnt_i) begin
              NS      = WAIT_RVALID;
            end else begin
              NS      = WAIT_GNT;
            end
          end else begin
            // we are requested to abort our current request
            if (clear_i)
              NS = WAIT_ABORTED;
          end
        end else begin
          // just wait for rvalid and go back to IDLE, no new request
          // requested
          instr_req_o = 1'b0;

          if (instr_rvalid_i) begin
            fifo_rdata_valid = 1'b1;
            NS = IDLE;
          end else begin
            if (clear_i)
              NS = WAIT_ABORTED;
          end
        end
      end // case: WAIT_RVALID

      // our last request was aborted, but we didn't yet get a rvalid and
      // there was no new request sent yet
      WAIT_ABORTED: begin
        if (req_i && fifo_addr_ready) begin
          // prepare for next request
          instr_req_o = 1'b1;

          if (instr_rvalid_i) begin
            fifo_addr_valid  = 1'b1;

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
      end

      default:
      begin
        NS          = IDLE;
        instr_req_o = 1'b0;
      end
    endcase
  end

  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      CS      <= IDLE;
    end
    else
    begin
      CS <= NS;
    end
  end

endmodule
