// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Prefetcher Buffer for 32 bit memory interface              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Buffer that caches instructions. This cuts overly //
//                 long critical paths to the instruction cache               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// input port: send address one cycle before the data
// clear_i clears the FIFO for the following cycle. in_addr_i can be sent in
// this cycle already
module riscv_fetch_fifo
(
    input  logic        clk,
    input  logic        rst_n,

    // control signals
    input  logic        branch_i,          // clears the contents of the fifo
    input  logic [31:0] addr_i,

    input  logic        hwlp_i,          // tries to insert an entry above the first one
    input  logic [31:0] hwlp_target_i,

    // input port
    input  logic        in_addr_valid_i,
    output logic        in_addr_ready_o,
    output logic [31:0] in_fetch_addr_o,
    input  logic        in_wait_gnt_i,

    input  logic        in_rdata_valid_i,
    output logic        in_rdata_ready_o,
    input  logic [31:0] in_rdata_i,

    // output port
    output logic        out_valid_o,
    input  logic        out_ready_i,
    output logic [31:0] out_rdata_o,
    output logic [31:0] out_addr_o,
    output logic        out_is_hwlp_o
  );

  localparam DEPTH = 3; // must be 2 or greater

  // index 0 is used for output
  logic [0:DEPTH-1] [31:0]  addr_n,        addr_int,        addr_Q;
  logic [0:DEPTH-1]         addr_valid_n,  addr_valid_int,  addr_valid_Q;
  logic [0:DEPTH-1] [31:0]  rdata_n,       rdata_int,       rdata_Q;
  logic [0:DEPTH-1]         rdata_valid_n, rdata_valid_int, rdata_valid_Q;
  logic [0:1      ]         is_hwlp_n,     is_hwlp_int,     is_hwlp_Q;

  logic             [31:0]  rdata, rdata_unaligned;
  logic                     valid, valid_unaligned;

  logic                     aligned_is_compressed, unaligned_is_compressed;

  logic [31:0]              fifo_last_addr;
  logic                     hwlp_inbound;


  //////////////////////////////////////////////////////////////////////////////
  // output port
  //////////////////////////////////////////////////////////////////////////////


  assign rdata = (rdata_valid_Q[0]) ? rdata_Q[0] : in_rdata_i;
  assign valid = (rdata_valid_Q[0] || (addr_valid_Q[0] && in_rdata_valid_i));

  assign rdata_unaligned = (rdata_valid_Q[1]) ? {rdata_Q[1][15:0], rdata[31:16]} : {in_rdata_i[15:0], rdata[31:16]};
  // it is implied that rdata_valid_Q[0] is set
  assign valid_unaligned = (rdata_valid_Q[1] || (addr_valid_Q[1] && in_rdata_valid_i));

  assign unaligned_is_compressed = rdata[17:16] != 2'b11;
  assign aligned_is_compressed   = rdata[1:0] != 2'b11;

  //////////////////////////////////////////////////////////////////////////////
  // instruction aligner (if unaligned)
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    // serve the aligned case even though the output address is unaligned when
    // the next instruction will be from a hardware loop target
    // in this case the current instruction is already prealigned in element 0
    if (out_addr_o[1] && (~is_hwlp_Q[1])) begin
      // unaligned case
      out_rdata_o = rdata_unaligned;

      if (unaligned_is_compressed)
        out_valid_o = valid;
      else
        out_valid_o = valid_unaligned;
    end else begin
      // aligned case
      out_rdata_o = rdata;
      out_valid_o = valid;
    end
  end

  assign out_addr_o    = addr_Q[0]; // always output addr directly since we sent it one cycle earlier to the FIFO
  assign out_is_hwlp_o = is_hwlp_Q[0];


  //////////////////////////////////////////////////////////////////////////////
  // input port
  //////////////////////////////////////////////////////////////////////////////

  // we accept addresses as long as our fifo is not full or we encounter
  // a branch or hwloop
  assign in_addr_ready_o = branch_i || (hwlp_i & (~is_hwlp_Q[1])) || (~addr_valid_Q[DEPTH-1]);

  // we accept data as long as our fifo is not full
  // we don't care about clear here as the data will be received one cycle
  // later anyway
  assign in_rdata_ready_o = ~rdata_valid_Q[DEPTH-1];


  // output the latest valid address we got
  int i;
  always_comb
  begin
    fifo_last_addr = addr_Q[0];

    for(i = 1; i < DEPTH; i++) begin
      if (addr_valid_Q[i])
        fifo_last_addr = addr_Q[i];
    end
  end

  always_comb
  begin
    in_fetch_addr_o = {fifo_last_addr[31:2], 2'b00} + 32'd4;

    if (in_wait_gnt_i) begin
      in_fetch_addr_o = {fifo_last_addr[31:2], 2'b00};

      if (hwlp_i & (~is_hwlp_Q[1]) & rdata_valid_Q[0])
        in_fetch_addr_o = hwlp_target_i;
    end else begin
      if (hwlp_i & (~is_hwlp_Q[1]))
        in_fetch_addr_o = hwlp_target_i;
    end

    // branches have priority since the fifo is cleared
    if (branch_i)
      in_fetch_addr_o = addr_i;

  end

  // accept hwloop input as long as our second entry is not already one and we
  // are valid, otherwise we might loose a part of an instruction
  assign hwlp_inbound = hwlp_i & (~is_hwlp_Q[1]) & out_valid_o;

  //////////////////////////////////////////////////////////////////////////////
  // FIFO management
  //////////////////////////////////////////////////////////////////////////////

  int j;
  always_comb
  begin
    addr_int        = addr_Q;
    addr_valid_int  = addr_valid_Q;
    is_hwlp_int     = is_hwlp_Q;

    if (in_addr_valid_i && in_addr_ready_o) begin
      for(j = 0; j < DEPTH; j++) begin
        if (~addr_valid_Q[j]) begin
          addr_int[j]       = in_fetch_addr_o;
          addr_valid_int[j] = 1'b1;

          break;
        end
      end
    end

    // on a hardware loop invalidate everything starting from the second entry
    if (hwlp_inbound) begin
      addr_int[1]               = in_fetch_addr_o;
      addr_valid_int[1]         = 1'b1;
      addr_valid_int[2:DEPTH-1] = '0;
      is_hwlp_int[1]            = 1'b1;
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

    // on a hardware loop invalidate everything starting from the second entry
    if (hwlp_inbound) begin
      rdata_int[0] = out_rdata_o; // save current output in rdata_int[0], so that we have it available even though we override entry #1
      rdata_valid_int[1:DEPTH-1] = '0;
    end
  end

  // move everything by one step
  always_comb
  begin
    addr_n           = addr_int;
    addr_valid_n     = addr_valid_int;
    rdata_n          = rdata_int;
    rdata_valid_n    = rdata_valid_int;
    is_hwlp_n        = is_hwlp_int;

    if (out_ready_i && out_valid_o) begin

      // now take care of the addresses
      if (is_hwlp_int[1]) begin
        // hardware loop found in second entry
        addr_n         = {addr_int[1][31:0], addr_int[2:DEPTH-1], 32'b0};
        addr_valid_n   = {addr_valid_int[1:DEPTH-1],  1'b0};
        rdata_n        = {rdata_int[1:DEPTH-1],      32'b0};
        rdata_valid_n  = {rdata_valid_int[1:DEPTH-1], 1'b0};
        is_hwlp_n      = {is_hwlp_int[1], 1'b0};

      end else begin
        // no hardware loop found
        if (addr_Q[0][1]) begin
          // unaligned case

          if (unaligned_is_compressed) begin
            addr_n         = {{addr_int[1][31:2], 2'b00}, addr_int[2:DEPTH-1], 32'b0};
          end else begin
            addr_n         = {{addr_int[1][31:2], 2'b10}, addr_int[2:DEPTH-1], 32'b0};
          end

          addr_valid_n   = {addr_valid_int[1:DEPTH-1],  1'b0};
          rdata_n        = {rdata_int[1:DEPTH-1],      32'b0};
          rdata_valid_n  = {rdata_valid_int[1:DEPTH-1], 1'b0};
          is_hwlp_n      = {is_hwlp_int[1], 1'b0};

        end else begin
          // aligned case

          if (aligned_is_compressed) begin
            // just increase address, do not move to next entry in FIFO
            addr_n[0]      = {addr_int[0][31:2], 2'b10};
            is_hwlp_n[0]   = 1'b0; // invalidate hwlp bit for current address
          end else begin
            // move to next entry in FIFO
            addr_n         = {{addr_int[1][31:2], 2'b00}, addr_int[2:DEPTH-1], 32'b0};
            addr_valid_n   = {addr_valid_int[1:DEPTH-1],  1'b0};
            rdata_n        = {rdata_int[1:DEPTH-1],      32'b0};
            rdata_valid_n  = {rdata_valid_int[1:DEPTH-1], 1'b0};
            is_hwlp_n      = {is_hwlp_int[1], 1'b0};
          end

        end
      end
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      addr_Q           <= '{default: '0};
      addr_valid_Q     <= '0;
      rdata_Q          <= '{default: '0};
      rdata_valid_Q    <= '0;
      is_hwlp_Q        <= '0;
    end
    else
    begin
      // on a clear signal from outside we invalidate the content of the FIFO
      // completely and start from an empty state
      if (branch_i) begin
        addr_Q[0]        <= in_fetch_addr_o;
        addr_valid_Q     <= {in_addr_valid_i, {DEPTH-1{1'b0}}};
        rdata_valid_Q    <= '0;
        is_hwlp_Q        <= '0;
      end else begin
        addr_Q           <= addr_n;
        addr_valid_Q     <= addr_valid_n;
        rdata_Q          <= rdata_n;
        rdata_valid_Q    <= rdata_valid_n;
        is_hwlp_Q        <= is_hwlp_n;
      end
    end
  end

endmodule

// branch_i deletes everything up to now, i.e. it assumes that addr_i now has
// the correct state and uses the current cycle's addr_i to fetch new data
module riscv_prefetch_buffer
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        req_i,

  input  logic        branch_i,
  input  logic [31:0] addr_i,

  input  logic        hwloop_i,
  input  logic [31:0] hwloop_target_i,

  input  logic        ready_i,
  output logic        valid_o,
  output logic [31:0] rdata_o,
  output logic [31:0] addr_o,
  output logic        is_hwlp_o, // is set when the currently served data is from a hwloop

  // goes to instruction memory / instruction cache
  output logic        instr_req_o,
  output logic [31:0] instr_addr_o,
  input  logic        instr_gnt_i,
  input  logic        instr_rvalid_i,
  input  logic [31:0] instr_rdata_i,

  // Prefetch Buffer Status
  output logic        busy_o
);

  enum logic [1:0] {IDLE, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED } CS, NS;

  logic [31:0] fetch_addr;

  logic        fifo_addr_valid;
  logic        fifo_addr_ready;

  logic        fifo_rdata_valid;
  logic        fifo_rdata_ready;

  logic        wait_gnt;


  //////////////////////////////////////////////////////////////////////////////
  // prefetch buffer status
  //////////////////////////////////////////////////////////////////////////////

  assign busy_o = (CS != IDLE) || instr_req_o;

  //////////////////////////////////////////////////////////////////////////////
  // fetch fifo
  // consumes addresses and rdata
  //////////////////////////////////////////////////////////////////////////////

  riscv_fetch_fifo fifo_i
  (
    .clk                   ( clk               ),
    .rst_n                 ( rst_n             ),

    .branch_i              ( branch_i          ),
    .addr_i                ( addr_i            ),

    .hwlp_i                ( hwloop_i          ),
    .hwlp_target_i         ( hwloop_target_i   ),

    .in_addr_valid_i       ( fifo_addr_valid   ),
    .in_addr_ready_o       ( fifo_addr_ready   ),
    .in_fetch_addr_o       ( fetch_addr        ),
    .in_wait_gnt_i         ( wait_gnt          ),

    .in_rdata_valid_i      ( fifo_rdata_valid  ),
    .in_rdata_ready_o      ( fifo_rdata_ready  ),
    .in_rdata_i            ( instr_rdata_i     ),

    .out_valid_o           ( valid_o           ),
    .out_ready_i           ( ready_i           ),
    .out_rdata_o           ( rdata_o           ),
    .out_addr_o            ( addr_o            ),
    .out_is_hwlp_o         ( is_hwlp_o         )
  );


  //////////////////////////////////////////////////////////////////////////////
  // instruction fetch FSM
  // deals with instruction memory / instruction cache
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    wait_gnt         = 1'b0;
    instr_req_o      = 1'b0;
    instr_addr_o     = fetch_addr;
    fifo_addr_valid  = 1'b0;
    fifo_rdata_valid = 1'b0;
    NS               = CS;

    unique case(CS)
      // default state, not waiting for requested data
      IDLE:
      begin
        instr_req_o = 1'b0;

        if ((req_i && fifo_addr_ready) || branch_i) begin
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
        wait_gnt    = 1'b1;
        instr_req_o = 1'b1;

        if (branch_i) begin
          fifo_addr_valid = 1'b1;
        end

        if(instr_gnt_i)
          NS = WAIT_RVALID;
        else
          NS = WAIT_GNT;
      end // case: WAIT_GNT

      // we wait for rvalid, after that we are ready to serve a new request
      WAIT_RVALID: begin

        if ((req_i && fifo_addr_ready) || branch_i) begin
          // prepare for next request

          if (instr_rvalid_i) begin
            instr_req_o      = 1'b1;
            fifo_rdata_valid = 1'b1;
            fifo_addr_valid  = 1'b1;

            if (instr_gnt_i) begin
              NS      = WAIT_RVALID;
            end else begin
              NS      = WAIT_GNT;
            end
          end else begin
            // we are requested to abort our current request
            // we didn't get an rvalid yet, so wait for it
            if (branch_i) begin
              fifo_addr_valid  = 1'b1;
              NS               = WAIT_ABORTED;
            end else if (hwloop_i & valid_o) begin
              NS               = WAIT_ABORTED;
            end
          end
        end else begin
          // just wait for rvalid and go back to IDLE, no new request

          if (instr_rvalid_i) begin
            fifo_rdata_valid = 1'b1;
            NS               = IDLE;
          end
        end
      end // case: WAIT_RVALID

      // our last request was aborted, but we didn't yet get a rvalid and
      // there was no new request sent yet
      // we assume that req_i is set to high
      WAIT_ABORTED: begin
        wait_gnt = 1'b1;

        if (instr_rvalid_i) begin
          instr_req_o  = 1'b1;
          // no need to send address, already done in WAIT_RVALID

          if (instr_gnt_i) begin
            NS      = WAIT_RVALID;
          end else begin
            NS      = WAIT_GNT;
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
      CS <= IDLE;
    end
    else
    begin
      CS <= NS;
    end
  end

endmodule
