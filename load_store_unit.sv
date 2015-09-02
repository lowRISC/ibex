////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                 DEI @ UNIBO - University of Bologna                        //
//                                                                            //
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
// Create Date:    01/07/2014                                                 //
// Design Name:    Load Store Unit                                            //
// Module Name:    load_store_unit.sv                                         //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Load Store Unit, used to eliminate multiple access during  //
//                 processor stalls, and to align bytes and halfwords         //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (August 6th 2014) Added stall stupport when ID stage is    //
//                 stalled                                                    //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


`include "defines.sv"

module load_store_unit
(
    input  logic         clk,
    input  logic         rst_n,

    // signals from ex stage
    input  logic         data_we_ex_i,         // write enable                      -> from ex stage
    input  logic [1:0]   data_type_ex_i,       // Data type word, halfword, byte    -> from ex stage
    input  logic [31:0]  data_wdata_ex_i,      // data to write to memory           -> from ex stage
    input  logic [1:0]   data_reg_offset_ex_i, // offset inside register for stores -> from ex stage
    input  logic         data_sign_ext_ex_i,   // sign extension                    -> from ex stage

    output logic [31:0]  data_rdata_ex_o,      // requested data                    -> to ex stage
    input  logic         data_req_ex_i,        // data request                      -> from ex stage
    input  logic [31:0]  data_addr_ex_i,       // data address                      -> from ex stage
    output logic         data_ack_int_o,       // data ack                          -> to controller

    input  logic         data_misaligned_ex_i, // misaligned access in last ld/st   -> from ID/EX pipeline
    output logic         data_misaligned_o,    // misaligned access was detected    -> to controller

    // output to data memory
    output logic         data_req_o,
    output logic [31:0]  data_addr_o,
    output logic         data_we_o,

    output logic [3:0]   data_be_o,
    output logic [31:0]  data_wdata_o,
    input  logic [31:0]  data_rdata_i,
    input  logic         data_rvalid_i,
    input  logic         data_gnt_i,

     // stall signal
    input  logic         ex_stall_i
);

  // registers for data_rdata alignment and sign extension
  logic [1:0]   data_type_q;
  logic [1:0]   rdata_offset_q;
  logic         data_sign_ext_q;

  logic [1:0]   wdata_offset;   // mux control for data to be written to memory

  // signals for tcdm contention
  logic [3:0]   data_be, data_be_q;
  logic [31:0]  data_wdata, data_wdata_q;
  logic         data_we_q;
  logic [31:0]  data_addr_q;

  logic         misaligned_st;   // high if we are currently performing the second part of a misaligned store
  logic         misaligned_st_q; // register for misaligned_st

  logic         request_entered;

  enum logic [2:0]  { IDLE, WAIT_GNT, PENDING_W_EX_STALL_2, PENDING_W_EX_STALL_1, PENDING_WO_EX_STALL} 	CS, NS;

  logic latch_rdata;
  logic [31:0]  rdata_q;

  ///////////////////////////////// BE generation ////////////////////////////////
  always_comb
  begin
    case (data_type_ex_i) // Data type 00 Word, 01 Half word, 11,10 byte
      2'b00:
      begin // Writing a word
        if (misaligned_st == 1'b0)
        begin // non-misaligned case
          case (data_addr_ex_i[1:0])
            2'b00: data_be = 4'b1111;
            2'b01: data_be = 4'b1110;
            2'b10: data_be = 4'b1100;
            2'b11: data_be = 4'b1000;
          endcase; // case (data_addr_ex_i[1:0])
        end
        else
        begin // misaligned case
          case (data_addr_ex_i[1:0])
            2'b00: data_be = 4'b0000; // this is not used, but included for completeness
            2'b01: data_be = 4'b0001;
            2'b10: data_be = 4'b0011;
            2'b11: data_be = 4'b0111;
          endcase; // case (data_addr_ex_i[1:0])
        end
      end

      2'b01:
      begin // Writing a half word
        if (misaligned_st == 1'b0)
        begin // non-misaligned case
          case (data_addr_ex_i[1:0])
            2'b00: data_be = 4'b0011;
            2'b01: data_be = 4'b0110;
            2'b10: data_be = 4'b1100;
            2'b11: data_be = 4'b1000;
          endcase; // case (data_addr_ex_i[1:0])
        end
        else
        begin // misaligned case
          data_be = 4'b0001;
        end
      end

      2'b10,
      2'b11: begin // Writing a byte
        case (data_addr_ex_i[1:0])
          2'b00: data_be = 4'b0001;
          2'b01: data_be = 4'b0010;
          2'b10: data_be = 4'b0100;
          2'b11: data_be = 4'b1000;
        endcase; // case (data_addr_ex_i[1:0])
      end
    endcase; // case (data_type_ex_i)
  end

  // prepare data to be written to the memory
  // we handle misaligned accesses, half word and byte accesses and
  // register offsets here
  assign wdata_offset = data_addr_ex_i[1:0] - data_reg_offset_ex_i[1:0];
  always_comb
  begin
    case (wdata_offset)
      2'b00: data_wdata = data_wdata_ex_i[31:0];
      2'b01: data_wdata = {data_wdata_ex_i[23:0], data_wdata_ex_i[31:24]};
      2'b10: data_wdata = {data_wdata_ex_i[15:0], data_wdata_ex_i[31:16]};
      2'b11: data_wdata = {data_wdata_ex_i[ 7:0], data_wdata_ex_i[31: 8]};
    endcase; // case (wdata_offset)
  end


  // FF for rdata
  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      data_type_q     <= '0;
      rdata_offset_q  <= '0;
      data_sign_ext_q <= '0;
    end
    else if (request_entered == 1'b1) // request entered FSM
    begin
      data_type_q     <= data_type_ex_i;
      rdata_offset_q  <= data_addr_ex_i[1:0];
      data_sign_ext_q <= data_sign_ext_ex_i;
    end
  end

  // pipeline gnt signal
  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      data_ack_int_o  <= 1'b0;
    end
    else
    begin
      data_ack_int_o  <= ~((data_req_o == 1'b1) & (data_gnt_i == 1'b0));
    end
  end

  // FF for not accepted requests
  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      data_be_q        <= '0;
      data_addr_q      <= '0;
      data_we_q        <= '0;
      data_wdata_q     <= '0;
      misaligned_st_q  <= 1'b0;
    end
    else if ((data_req_o == 1'b1) & (data_gnt_i == 1'b0)) // request was not granted
    begin
      data_be_q       <= data_be_o;
      data_addr_q     <= data_addr_o;
      data_we_q       <= data_we_o;
      data_wdata_q    <= data_wdata_o;
      misaligned_st_q <= misaligned_st;
    end
  end

  ////////////////////////////////////////////////////////////////////////
  //  ____  _               _____      _                 _              //
  // / ___|(_) __ _ _ __   | ____|_  _| |_ ___ _ __  ___(_) ___  _ __   //
  // \___ \| |/ _` | '_ \  |  _| \ \/ / __/ _ \ '_ \/ __| |/ _ \| '_ \  //
  //  ___) | | (_| | | | | | |___ >  <| ||  __/ | | \__ \ | (_) | | | | //
  // |____/|_|\__, |_| |_| |_____/_/\_\\__\___|_| |_|___/_|\___/|_| |_| //
  //          |___/                                                     //
  ////////////////////////////////////////////////////////////////////////

  logic [31:0] data_rdata_ext;

  logic [31:0] rdata_w_ext; // sign extension for words, actually only misaligned assembly
  logic [31:0] rdata_h_ext; // sign extension for half words
  logic [31:0] rdata_b_ext; // sign extension for bytes

  // take care of misaligned words
  always_comb
  begin
    case (rdata_offset_q)
      2'b00: rdata_w_ext = data_rdata_i[31:0];
      2'b01: rdata_w_ext = {data_rdata_i[ 7:0], rdata_q[31:8]};
      2'b10: rdata_w_ext = {data_rdata_i[15:0], rdata_q[31:16]};
      2'b11: rdata_w_ext = {data_rdata_i[23:0], rdata_q[31:24]};
    endcase
  end

  // sign extension for half words
  always_comb
  begin
    case (rdata_offset_q)
      2'b00:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
        else
          rdata_h_ext = {{16{data_rdata_i[15]}}, data_rdata_i[15:0]};
      end

      2'b01:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_h_ext = {16'h0000, data_rdata_i[23:8]};
        else
          rdata_h_ext = {{16{data_rdata_i[23]}}, data_rdata_i[23:8]};
      end

      2'b10:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_h_ext = {16'h0000, data_rdata_i[31:16]};
        else
          rdata_h_ext = {{16{data_rdata_i[31]}}, data_rdata_i[31:16]};
      end

      2'b11:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_h_ext = {16'h0000, data_rdata_i[7:0], rdata_q[31:24]};
        else
          rdata_h_ext = {{16{data_rdata_i[7]}}, data_rdata_i[7:0], rdata_q[31:24]};
      end
    endcase // case (rdata_offset_q)
  end

  // sign extension for bytes
  always_comb
  begin
    case (rdata_offset_q)
      2'b00:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
        else
          rdata_b_ext = {{24{data_rdata_i[7]}}, data_rdata_i[7:0]};
      end

      2'b01: begin
        if (data_sign_ext_q == 1'b0)
          rdata_b_ext = {24'h00_0000, data_rdata_i[15:8]};
        else
          rdata_b_ext = {{24{data_rdata_i[15]}}, data_rdata_i[15:8]};
      end

      2'b10:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_b_ext = {24'h00_0000, data_rdata_i[23:16]};
        else
          rdata_b_ext = {{24{data_rdata_i[23]}}, data_rdata_i[23:16]};
      end

      2'b11:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_b_ext = {24'h00_0000, data_rdata_i[31:24]};
        else
          rdata_b_ext = {{24{data_rdata_i[31]}}, data_rdata_i[31:24]};
      end
    endcase // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb
  begin
    case (data_type_q)
      2'b00:       data_rdata_ext = rdata_w_ext;
      2'b01:       data_rdata_ext = rdata_h_ext;
      2'b10,2'b11: data_rdata_ext = rdata_b_ext;
    endcase //~case(rdata_type_q)
  end



  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      CS            <= IDLE;
      rdata_q       <= '0;
    end
    else
    begin
      CS            <= NS;

      if(latch_rdata)
      begin
        // if we have detected a misaligned access, and we are
        // currently doing the first part of this access, then
        // store the data coming from memory in rdata_q.
        // In all other cases, rdata_q gets the value that we are
        // writing to the register file
        if ((data_misaligned_ex_i == 1'b1) || (data_misaligned_o == 1'b1))
          rdata_q  <= data_rdata_i;
        else
          rdata_q  <= data_rdata_ext;
      end
    end
  end

  // output to register file
  assign data_rdata_ex_o = (latch_rdata == 1'b1) ? data_rdata_ext : rdata_q;


  // FSM
  always_comb
  begin
    data_req_o         = 1'b0;
    data_we_o          = 1'b0;
    data_addr_o        = data_addr_ex_i;
    data_wdata_o       = data_wdata;
    data_be_o          = data_be;
    misaligned_st      = data_misaligned_ex_i;
    latch_rdata        = 1'b0;
    request_entered    = 1'b0;

    case(CS)
      IDLE:
      begin
        data_req_o         = data_req_ex_i;
        data_we_o          = data_we_ex_i;

        if(data_req_ex_i)
        begin
          request_entered = 1'b1;

          if(data_gnt_i)
          begin
            if(ex_stall_i)
              NS = PENDING_W_EX_STALL_1;
            else
              NS = PENDING_WO_EX_STALL;
            end
          else
          begin
            if(ex_stall_i)
              NS = IDLE;
            else
            begin
              NS = WAIT_GNT;
            end
          end
        end
        else
          NS = IDLE;
      end //~ IDLE

      WAIT_GNT:
      begin
        data_req_o        = 1'b1;
        data_we_o         = data_we_q;

        data_addr_o       = data_addr_q;
        data_be_o         = data_be_q;
        data_wdata_o      = data_wdata_q;
        misaligned_st     = misaligned_st_q;

        if(data_gnt_i)
        begin
          NS = PENDING_WO_EX_STALL;
        end
             else
        begin
          NS = WAIT_GNT;
        end
      end // case: WAIT_GNT

      PENDING_WO_EX_STALL:
      begin
        latch_rdata        = ~data_we_o;

        data_req_o         = data_req_ex_i;
        data_we_o          = data_we_ex_i;

        if(data_req_ex_i)
        begin
          request_entered = 1'b1;

          if(data_gnt_i)
          begin
            if(ex_stall_i)
              NS = PENDING_W_EX_STALL_1;
            else
              NS = PENDING_WO_EX_STALL;
          end
          else
          begin
            if(ex_stall_i)
              NS = IDLE;
            else
              NS = WAIT_GNT;
          end
        end
        else
          NS = IDLE;
      end //~PENDING_WO_EX_STALL

      PENDING_W_EX_STALL_1 :
      begin
        data_req_o     = 1'b0;

        latch_rdata    = ~data_we_o;

        if(ex_stall_i)
        begin
          NS = PENDING_W_EX_STALL_2;
        end
        else
        begin
          NS = IDLE;
        end
      end //~ PENDING_W_EX_STALL_1

      PENDING_W_EX_STALL_2 :
      begin
        if(ex_stall_i)
        begin
          NS = PENDING_W_EX_STALL_2;
        end
        else
        begin
          NS = IDLE;
        end
      end //~ PENDING_W_EX_STALL_2

      default :
      begin
        NS = IDLE;
      end
    endcase
  end

  // check for misaligned accesses that need a second memory access
  // If one is detected, this is signaled with data_misaligned_o to
  // the controller which selectively stalls the pipeline
  always_comb
  begin
    data_misaligned_o = 1'b0;

    if((data_req_ex_i == 1'b1) && (data_misaligned_ex_i == 1'b0))
    begin
      case (data_type_ex_i)
        2'b00: // word
        begin
          if(data_addr_ex_i[1:0] != 2'b00)
            data_misaligned_o = 1'b1;
        end
        2'b01: // half word
        begin
          if(data_addr_ex_i[1:0] == 2'b11)
            data_misaligned_o = 1'b1;
        end
      endcase // case (data_type_ex_i)
    end
  end

endmodule
