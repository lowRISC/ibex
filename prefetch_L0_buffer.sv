////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                 DEI @ UNIBO - University of Bologna                        //
//                                                                            //
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Create Date:    06/08/2014                                                 //
// Design Name:    RISC-V processor core                                      //
// Module Name:    prefetch_buffer.sv                                         //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Buffer that caches instructions. This cuts overly //
//                 long critical paths to the instruction cache               //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module riscv_prefetch_L0_buffer
#(
  parameter                                   RDATA_IN_WIDTH = 128
)
(
  input  logic                                clk,
  input  logic                                rst_n,

  input  logic                                req_i,

  input  logic                                branch_i,
  input  logic [31:0]                         addr_i,

  input  logic                                hwloop_i,
  input  logic [31:0]                         hwloop_target_i,

  input  logic                                ready_i,
  output logic                                valid_o,
  output logic [31:0]                         rdata_o,
  output logic [31:0]                         addr_o,
  output logic                                is_hwlp_o, // is set when the currently served data is from a hwloop

  // goes to instruction memory / instruction cache
  output logic                                instr_req_o,
  output logic [31:0]                         instr_addr_o,
  input  logic                                instr_gnt_i,
  input  logic                                instr_rvalid_i,
  input  logic [RDATA_IN_WIDTH/32-1:0][31:0]  instr_rdata_i,

  // Prefetch Buffer Status
  output logic                                busy_o
);

  logic                               busy_L0;

  enum logic [2:0] { REGULAR, PREFETCH, LAST_BRANCH, LAST_BRANCH_WAIT, HWLP_WAIT_LAST, HWLP_FETCHING, HWLP_PREFETCH, HWLP_ABORT } prefetch_CS, prefetch_NS;
  logic                               do_prefetch;
  logic                       [31:0]  addr_q, addr_n, addr_int, addr_aligned_next;

  logic                       [31:0]  rdata_last_q;

  logic                               valid_L0;
  logic [RDATA_IN_WIDTH/32-1:0][31:0] rdata_L0;
  logic                        [31:0] addr_L0;

  // prepared data for output
  logic                        [31:0] rdata, rdata_unaligned;
  logic                               valid, valid_unaligned;

  logic                               aligned_is_compressed, unaligned_is_compressed;

  logic                               fetching_hwlp;
  logic                               hwlp_inhibit;
  logic                               prefetch_important;


  prefetch_L0_buffer_L0
  #(
    .RDATA_IN_WIDTH ( RDATA_IN_WIDTH )
  )
  L0_buffer_i
  (
    .clk                  ( clk                ),
    .rst_n                ( rst_n              ),

    .prefetch_i           ( do_prefetch        ),
    .prefetch_important_i ( prefetch_important ),
    .prefetch_addr_i      ( addr_aligned_next  ),

    .branch_i             ( branch_i           ),
    .branch_addr_i        ( addr_i             ),

    .hwlp_i               ( hwloop_i & (~hwlp_inhibit) ),
    .hwlp_addr_i          ( hwloop_target_i    ),

    .hwlp_fetching_o      ( fetching_hwlp      ),

    .valid_o              ( valid_L0           ),
    .rdata_o              ( rdata_L0           ),
    .addr_o               ( addr_L0            ),

    .instr_req_o          ( instr_req_o        ),
    .instr_addr_o         ( instr_addr_o       ),
    .instr_gnt_i          ( instr_gnt_i        ),
    .instr_rvalid_i       ( instr_rvalid_i     ),
    .instr_rdata_i        ( instr_rdata_i      ),

    .busy_o               ( busy_L0            )
  );


  assign rdata = ((prefetch_CS == PREFETCH) | (prefetch_CS == HWLP_WAIT_LAST) | (prefetch_CS == HWLP_PREFETCH) | (prefetch_CS == LAST_BRANCH_WAIT)) ? rdata_last_q : rdata_L0[addr_o[3:2]];
  assign valid = ( ((prefetch_CS == PREFETCH) | (prefetch_CS == HWLP_WAIT_LAST) | (prefetch_CS == HWLP_PREFETCH)) | valid_L0) & (prefetch_CS != HWLP_ABORT);

  // the lower part of rdata_unaligned is always the higher part of rdata
  assign rdata_unaligned[15:0] = rdata[31:16];

  always_comb
  begin
    valid_unaligned = 1'b0;

    if (valid_L0) begin
      case(addr_o[3:2])
         2'b00: begin rdata_unaligned[31:16] = rdata_L0[1][15:0]; valid_unaligned = 1'b1; end
         2'b01: begin rdata_unaligned[31:16] = rdata_L0[2][15:0]; valid_unaligned = 1'b1; end
         2'b10: begin rdata_unaligned[31:16] = rdata_L0[3][15:0]; valid_unaligned = 1'b1; end
         // this state is only interesting if we have already done a prefetch
         2'b11: begin
           rdata_unaligned[31:16] = rdata_L0[0][15:0];

           if ((prefetch_CS == PREFETCH) | (prefetch_CS == HWLP_PREFETCH)) begin
             valid_unaligned = 1'b1;
           end else begin
             valid_unaligned = 1'b0;
           end
         end
      endcase // addr_o
    end
  end


  assign unaligned_is_compressed = rdata[17:16] != 2'b11;
  assign aligned_is_compressed   = rdata[1:0] != 2'b11;

  assign addr_aligned_next = { addr_o[31:2], 2'b00 } + 32'h4;

  always_comb
  begin
    addr_int    = addr_o;

    // advance address when pipeline is unstalled
    if (ready_i) begin

      if (addr_o[1]) begin
        // unaligned case
        // always move to next entry in the FIFO

        if (unaligned_is_compressed) begin
          addr_int = { addr_aligned_next[31:2], 2'b00};
        end else begin
          addr_int = { addr_aligned_next[31:2], 2'b10};
        end

      end else begin
        // aligned case

        if (aligned_is_compressed) begin
          // just increase address, do not move to next entry in the FIFO
          addr_int = { addr_o[31:2], 2'b10 };
        end else begin
          // move to next entry in the FIFO
          addr_int = { addr_aligned_next[31:2], 2'b00 };
        end
      end

    end
  end

  always_comb
  begin
    do_prefetch = 1'b0;
    prefetch_NS = prefetch_CS;
    addr_n      = addr_int;

    case (prefetch_CS)
      REGULAR: begin
        if (fetching_hwlp) begin
          if (ready_i) begin
            addr_n      = hwloop_target_i;
            prefetch_NS = HWLP_FETCHING;
          end
          else
            prefetch_NS = HWLP_WAIT_LAST;
        end else if (addr_o[3:2] == 2'b11) begin
          if ((~addr_o[1]) & aligned_is_compressed & valid)
            // we are serving a compressed instruction
            prefetch_NS = PREFETCH;
          else begin
            if (ready_i)
              prefetch_NS = REGULAR;
            else if (valid_L0)
              prefetch_NS = PREFETCH;
          end
        end

        // actually only needed when ~branch_i and ~fetching_hwlp not set, but
        // if we would keep those as conditions, we generate a cominational loop
        if (addr_o[3:2] == 2'b11)
          do_prefetch = 1'b1;
      end

      // we are doing a prefetch
      // we save the last word of the L0 buffer and already preload the L0
      // buffer with new stuff
      PREFETCH: begin
        if (fetching_hwlp) begin
          if (ready_i) begin
            addr_n      = hwloop_target_i;
            prefetch_NS = HWLP_FETCHING;
          end
          else
            prefetch_NS = HWLP_WAIT_LAST;
        end else if (ready_i) begin
          if (hwloop_i) begin
            addr_n      = addr_q;
            prefetch_NS = HWLP_ABORT;
          end else begin
            if ((~addr_o[1]) & aligned_is_compressed)
              // we are serving a compressed instruction
              prefetch_NS = PREFETCH;
            else
              prefetch_NS = REGULAR;
          end
        end
      end

      // we have branched into the last word of the L0 buffer, so we have to
      // prefetch the next cache line as soon as we got this one
      LAST_BRANCH: begin
        do_prefetch = 1'b1;

        if (valid_L0) begin
          if (fetching_hwlp) begin
            if (ready_i) begin
              addr_n      = hwloop_target_i;
              prefetch_NS = HWLP_FETCHING;
            end
            else
              prefetch_NS = HWLP_WAIT_LAST;
          end
          else if ( ((~addr_o[1]) & aligned_is_compressed) | (addr_o[1] & (~unaligned_is_compressed)) )
            // we are serving a compressed instruction or an instruction that
            // spans two cache lines
            prefetch_NS = PREFETCH;
          else if (ready_i)
            prefetch_NS = REGULAR;
          else
            prefetch_NS = LAST_BRANCH_WAIT;
        end
      end

      LAST_BRANCH_WAIT: begin
        if (ready_i)
          prefetch_NS = REGULAR;
      end

      // wait for last instruction to be delivered before going to hwloop
      HWLP_WAIT_LAST: begin
        if (ready_i) begin
          addr_n = addr_L0; // use address that was saved in L0 buffer
          prefetch_NS = HWLP_FETCHING;
        end
      end

      HWLP_FETCHING: begin
        if (valid_L0) begin
          if (addr_o[3:2] == 2'b11) begin
            do_prefetch = 1'b1;

            if ((~addr_o[1]) & aligned_is_compressed)
              // we are serving a compressed instruction
              prefetch_NS = HWLP_PREFETCH;
            else begin
              if (ready_i)
                prefetch_NS = REGULAR;
              else
                prefetch_NS = HWLP_PREFETCH;
            end
          end else begin
            if (ready_i) begin
              prefetch_NS = REGULAR;
            end
          end
        end
      end

      HWLP_PREFETCH: begin
        if (ready_i) begin
          prefetch_NS = REGULAR;
        end
      end

      HWLP_ABORT: begin
        if (fetching_hwlp) begin
          prefetch_NS = HWLP_FETCHING;
          addr_n      = hwloop_target_i;
        end
      end
    endcase

    // branches always have priority
    if (branch_i) begin
      addr_n = addr_i;
      if (addr_i[3:2] == 2'b11)
        prefetch_NS = LAST_BRANCH;
      else
        prefetch_NS = REGULAR;
    end
  end

  // do not abort an important prefetch for a hardware loop
  //assign prefetch_important = (((addr_q[3:1] == 3'b111) & (~unaligned_is_compressed)) | (addr_q[3:2] == 2'b00)) & do_prefetch;
  assign prefetch_important = 1'b0;

  assign hwlp_inhibit = (prefetch_CS == HWLP_WAIT_LAST) | (prefetch_CS == HWLP_FETCHING) | (prefetch_CS == HWLP_PREFETCH);


  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (~rst_n)
    begin
      addr_q         <= '0;
      prefetch_CS    <= REGULAR;
      rdata_last_q   <= '0;
    end
    else
    begin
      addr_q <= addr_n;

      prefetch_CS <= prefetch_NS;

      if (fetching_hwlp)
        rdata_last_q <= rdata_o;
      else if (do_prefetch)
        rdata_last_q <= rdata;

    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // output ports
  //////////////////////////////////////////////////////////////////////////////

  assign rdata_o = (~addr_o[1] | (prefetch_CS == HWLP_WAIT_LAST)) ? rdata: rdata_unaligned;
  assign valid_o = (addr_o[1] & (~unaligned_is_compressed)) ? valid_unaligned : valid;

  assign addr_o = addr_q;

  assign is_hwlp_o = ((prefetch_CS == HWLP_FETCHING) | (prefetch_CS == HWLP_PREFETCH)) & valid_o;

  assign busy_o = busy_L0;


  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

  // there should never be a ready_i without valid_o
  assert property (
    @(posedge clk) (ready_i) |-> (valid_o) ) else $warning("IF Stage is ready without prefetcher having valid data");

endmodule // prefetch_L0_buffer


module prefetch_L0_buffer_L0
#(
  parameter                                   RDATA_IN_WIDTH = 128
)
(
  input  logic                                clk,
  input  logic                                rst_n,

  input  logic                                prefetch_i,
  input  logic                                prefetch_important_i,
  input  logic [31:0]                         prefetch_addr_i,

  input  logic                                branch_i,
  input  logic [31:0]                         branch_addr_i,

  input  logic                                hwlp_i,
  input  logic [31:0]                         hwlp_addr_i,


  output logic                                hwlp_fetching_o,

  output logic                                valid_o,
  output logic [RDATA_IN_WIDTH/32-1:0][31:0]  rdata_o,
  output logic [31:0]                         addr_o,

  // goes to instruction memory / instruction cache
  output logic                                instr_req_o,
  output logic [31:0]                         instr_addr_o,
  input  logic                                instr_gnt_i,
  input  logic                                instr_rvalid_i,
  input  logic [RDATA_IN_WIDTH/32-1:0][31:0]  instr_rdata_i,

  output logic                                busy_o
);

  enum logic [2:0] { EMPTY, VALID_L0, WAIT_GNT, WAIT_RVALID, ABORTED_BRANCH, WAIT_HWLOOP } CS, NS;

  logic [3:0][31:0]   L0_buffer;
  logic      [31:0]   addr_q, instr_addr_int;
  logic               valid;

  logic               hwlp_pending_n;


  // edge detector on hwlp pending
  assign hwlp_fetching_o  = (~hwlp_pending_n) & (hwlp_i);

  //////////////////////////////////////////////////////////////////////////////
  // FSM
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    NS             = CS;
    valid          = 1'b0;
    instr_req_o    = 1'b0;
    instr_addr_int = 'x;
    hwlp_pending_n = hwlp_i;

    case(CS)

      // wait for the first branch request before fetching any instructions
      EMPTY:
      begin
        if (branch_i)
          instr_addr_int = branch_addr_i;
        else if (hwlp_i & (~prefetch_important_i)) begin
          instr_addr_int = hwlp_addr_i;
          hwlp_pending_n = 1'b0;
        end
        else
          instr_addr_int = prefetch_addr_i;

        if (branch_i | hwlp_i | prefetch_i) // make the request to icache
        begin
          instr_req_o    = 1'b1;

          if (instr_gnt_i)
            NS = WAIT_RVALID;
          else
            NS = WAIT_GNT;
        end
      end //~EMPTY

      WAIT_GNT:
      begin
        if (branch_i)
          instr_addr_int = branch_addr_i;
        else
          instr_addr_int = addr_q;

        if (branch_i)
        begin
          instr_req_o    = 1'b1;

          if (instr_gnt_i)
            NS = WAIT_RVALID;
          else
            NS = WAIT_GNT;
        end
        else
        begin
          instr_req_o    = 1'b1;

          if (instr_gnt_i)
            NS = WAIT_RVALID;
          else
            NS = WAIT_GNT;
        end
      end //~WAIT_GNT


      WAIT_RVALID:
      begin
        valid   = instr_rvalid_i;

        if (branch_i)
          instr_addr_int = branch_addr_i;
        else if (hwlp_i)
          instr_addr_int = hwlp_addr_i;
        else
          instr_addr_int = prefetch_addr_i;

        if (branch_i)
        begin
          if (instr_rvalid_i)
          begin
            instr_req_o    = 1'b1;

            if (instr_gnt_i)
              NS = WAIT_RVALID;
            else
              NS = WAIT_GNT;
          end else begin
            NS = ABORTED_BRANCH; // TODO: THIS STATE IS IDENTICAL WITH THIS ONE
          end

        end
        else if (hwlp_i)
        begin

          if (instr_rvalid_i)
          begin
            instr_req_o    = 1'b1;
            hwlp_pending_n = 1'b0;

            if (instr_gnt_i)
              NS = WAIT_RVALID;
            else
              NS = WAIT_GNT;
          end else begin
            NS = WAIT_HWLOOP;
          end

        end
        else
        begin

          if (instr_rvalid_i)
          begin

            if (prefetch_i) // we are receiving the last packet, then prefetch the next one
            begin
              instr_req_o    = 1'b1;

              if (instr_gnt_i)
                NS = WAIT_RVALID;
              else
                NS = WAIT_GNT;
            end
            else // not the last chunk
            begin
              NS = VALID_L0;
            end
          end
        end
      end //~WAIT_RVALID

      VALID_L0:
      begin
        valid   = 1'b1;

        if (branch_i)
          instr_addr_int = branch_addr_i;
        else if (hwlp_i) begin
          instr_addr_int = hwlp_addr_i;
          hwlp_pending_n = 1'b0;
        end
        else
          instr_addr_int = prefetch_addr_i;

        if (branch_i | hwlp_i | prefetch_i)
        begin
          instr_req_o    = 1'b1;

          if (instr_gnt_i)
            NS = WAIT_RVALID;
          else
            NS = WAIT_GNT;
        end
      end //~VALID_L0

      ABORTED_BRANCH:
      begin

        // prepare address even if we don't need it
        // this removes the dependency for instr_addr_o on instr_rvalid_i
        if (branch_i)
          instr_addr_int = branch_addr_i;
        else
          instr_addr_int = addr_q;

        if (instr_rvalid_i)
        begin
          instr_req_o    = 1'b1;

          if (instr_gnt_i)
            NS = WAIT_RVALID;
          else
            NS = WAIT_GNT;
        end
      end //~ABORTED_BRANCH

      WAIT_HWLOOP:
      begin
        valid = instr_rvalid_i;

        // prepare address even if we don't need it
        // this removes the dependency for instr_addr_o on instr_rvalid_i
        if (branch_i)
          instr_addr_int = branch_addr_i;
        else
          instr_addr_int = addr_q;

        if (instr_rvalid_i)
        begin
          hwlp_pending_n = 1'b0;
          instr_req_o    = 1'b1;

          if (instr_gnt_i)
            NS = WAIT_RVALID;
          else
            NS = WAIT_GNT;
        end
      end //~ABORTED_HWLOOP

      default:
      begin
         NS = EMPTY;
      end
    endcase //~CS
  end


  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (~rst_n)
    begin
      CS             <= EMPTY;
      L0_buffer      <= '0;
      addr_q         <= '0;
    end
    else
    begin
      CS             <= NS;

      if (instr_rvalid_i)
      begin
        L0_buffer <= instr_rdata_i;
      end

      if (branch_i | hwlp_i | prefetch_i)
        addr_q <= instr_addr_int;
    end
  end


  //////////////////////////////////////////////////////////////////////////////
  // output ports
  //////////////////////////////////////////////////////////////////////////////

  assign instr_addr_o = { instr_addr_int[31:4], 4'b0000 };

  assign rdata_o = (instr_rvalid_i) ? instr_rdata_i : L0_buffer;
  assign addr_o  = addr_q;

  assign valid_o = valid & (~branch_i);

  assign busy_o = (CS != EMPTY) && (CS != VALID_L0) || instr_req_o;

endmodule
