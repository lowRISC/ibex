// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Load Store Unit
 *
 * Load Store Unit, used to eliminate multiple access during processor stalls,
 * and to align bytes and halfwords.
 */

`include "prim_assert.sv"
`include "dv_fcov_macros.svh"

module alt_lsu #(
  parameter bit          MemECC       = 1'b0,
  parameter int unsigned MemDataWidth = MemECC ? 32 + 7 : 32
) (
  input  logic         clk_i,
  input  logic         rst_ni,

  // data interface
  output logic         data_req_o,
  input  logic         data_gnt_i,
  input  logic         data_rvalid_i,
  input  logic         data_bus_err_i,
  input  logic         data_pmp_err_i,

  output logic [31:0]             data_addr_o,
  output logic                    data_we_o,
  output logic [3:0]              data_be_o,
  output logic [MemDataWidth-1:0] data_wdata_o,
  input  logic [MemDataWidth-1:0] data_rdata_i,

  // signals to/from ID/EX stage
  input  logic         lsu_we_i,             // write enable                     -> from ID/EX
  input  logic [1:0]   lsu_type_i,           // data type: word, half word, byte -> from ID/EX
  input  logic [31:0]  lsu_wdata_i,          // data to write to memory          -> from ID/EX
  input  logic         lsu_sign_ext_i,       // sign extension                   -> from ID/EX

  output logic [31:0]  lsu_rdata_o,          // requested data                   -> to ID/EX
  output logic         lsu_rdata_valid_o,
  input  logic         lsu_req_i,            // data request                     -> from ID/EX

  input  logic [31:0]  adder_result_ex_i,    // address computed in ALU          -> from ID/EX

  output logic         addr_incr_req_o,      // request address increment for
                                              // misaligned accesses              -> to ID/EX
  output logic [31:0]  addr_last_o,          // address of last transaction      -> to controller
                                              // -> mtval
                                              // -> AGU for misaligned accesses

  output logic         lsu_req_done_o,       // Signals that data request is complete
                                              // (only need to await final data
                                              // response)                        -> to ID/EX

  output logic         lsu_resp_valid_o,     // LSU has response from transaction -> to ID/EX

  // exception signals
  output logic         load_err_o,
  output logic         load_reXsp_intg_err_o,
  output logic         store_err_o,
  output logic         store_resp_intg_err_o,

  output logic         busy_o,

  output logic         perf_load_o,
  output logic         perf_store_o,

  input logic [31:0] addr_last_q,
  input logic [31:8] rdata_q,
  input logic [1:0] rdata_offset_q,
  input logic [1:0] data_type_q,
  input logic data_sign_ext_q,
  input logic data_we_q,
  input logic handle_misaligned_q,
  input logic pmp_err_q,
  input logic lsu_err_q
);

  logic [31:0]  data_addr;
  logic [31:0]  data_addr_w_aligned;
  logic [31:0]  addr_last_d;

  logic         addr_update;
  logic         ctrl_update;
  logic         rdata_update;

  logic [1:0]   data_offset;   // mux control for data to be written to memory

  logic [3:0]   data_be;
  logic [31:0]  data_wdata;

  logic [31:0]  data_rdata_ext;

  logic [31:0]  rdata_w_ext; // word realignment for misaligned loads
  logic [31:0]  rdata_h_ext; // sign extension for half words
  logic [31:0]  rdata_b_ext; // sign extension for bytes

  logic         split_misaligned_access;
  logic         handle_misaligned_d; // high after receiving grant for first
                                                          // part of a misaligned access
  logic         pmp_err_d;
  logic         lsu_err_d;
  logic         data_intg_err, data_or_pmp_err;

  assign data_addr   = adder_result_ex_i;
  assign data_offset = data_addr[1:0];

  // Store last address for mtval + AGU for misaligned transactions.  Do not update in case of
  // errors, mtval needs the (first) failing address.  Where an aligned access or the first half of
  // a misaligned access sees an error provide the calculated access address. For the second half of
  // a misaligned access provide the word aligned address of the second half.
  assign addr_last_d = addr_incr_req_o ? data_addr_w_aligned : data_addr;

  // take care of misaligned words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00:   rdata_w_ext =  data_rdata_i[31:0];
      2'b01:   rdata_w_ext = {data_rdata_i[ 7:0], rdata_q[31:8]};
      2'b10:   rdata_w_ext = {data_rdata_i[15:0], rdata_q[31:16]};
      2'b11:   rdata_w_ext = {data_rdata_i[23:0], rdata_q[31:24]};
      default: rdata_w_ext =  data_rdata_i[31:0];
    endcase
  end

  ////////////////////
  // Sign extension //
  ////////////////////

  // sign extension for half words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[15]}}, data_rdata_i[15:0]};
        end
      end

      2'b01: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[23:8]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[23]}}, data_rdata_i[23:8]};
        end
      end

      2'b10: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[31:16]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[31]}}, data_rdata_i[31:16]};
        end
      end

      2'b11: begin
        if (!data_sign_ext_q) begin
          rdata_h_ext = {16'h0000, data_rdata_i[7:0], rdata_q[31:24]};
        end else begin
          rdata_h_ext = {{16{data_rdata_i[7]}}, data_rdata_i[7:0], rdata_q[31:24]};
        end
      end

      default: rdata_h_ext = {16'h0000, data_rdata_i[15:0]};
    endcase // case (rdata_offset_q)
  end

  // sign extension for bytes
  always_comb begin
    unique case (rdata_offset_q)
      2'b00: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[7]}}, data_rdata_i[7:0]};
        end
      end

      2'b01: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[15:8]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[15]}}, data_rdata_i[15:8]};
        end
      end

      2'b10: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[23:16]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[23]}}, data_rdata_i[23:16]};
        end
      end

      2'b11: begin
        if (!data_sign_ext_q) begin
          rdata_b_ext = {24'h00_0000, data_rdata_i[31:24]};
        end else begin
          rdata_b_ext = {{24{data_rdata_i[31]}}, data_rdata_i[31:24]};
        end
      end

      default: rdata_b_ext = {24'h00_0000, data_rdata_i[7:0]};
    endcase // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb begin
    unique case (data_type_q)
      2'b00:       data_rdata_ext = rdata_w_ext;
      2'b01:       data_rdata_ext = rdata_h_ext;
      2'b10,2'b11: data_rdata_ext = rdata_b_ext;
      default:     data_rdata_ext = rdata_w_ext;
    endcase // case (data_type_q)
  end

  ///////////////////////////////
  // Read data integrity check //
  ///////////////////////////////

  assign data_intg_err = 1'b0;

  /////////////
  // LSU FSM //
  /////////////

  // check for misaligned accesses that need to be split into two word-aligned accesses
  assign split_misaligned_access =
      ((lsu_type_i == 2'b00) && (data_offset != 2'b00)) || // misaligned word access
      ((lsu_type_i == 2'b01) && (data_offset == 2'b11));   // misaligned half-word access

  /////////////
  // Outputs //
  /////////////

  assign data_or_pmp_err    = lsu_err_q | data_bus_err_i | pmp_err_q;
  assign lsu_resp_valid_o   = (data_rvalid_i | pmp_err_q);
  assign lsu_rdata_valid_o  =
    data_rvalid_i & ~data_or_pmp_err & ~data_we_q & ~data_intg_err;

  // output to register file
  assign lsu_rdata_o = data_rdata_ext;

  // output data address must be word aligned
  assign data_addr_w_aligned = {data_addr[31:2], 2'b00};

  // output to data interface
  assign data_addr_o   = data_addr_w_aligned;
  assign data_we_o     = lsu_we_i;
  assign data_be_o     = data_be;

  /////////////////////////////////////
  // Write data integrity generation //
  /////////////////////////////////////

  // SEC_CM: BUS.INTEGRITY
  assign data_wdata_o = data_wdata;

  // output to ID stage: mtval + AGU for misaligned transactions
  assign addr_last_o   = addr_last_q;

  // Signal a load or store error depending on the transaction type outstanding
  assign load_err_o      = data_or_pmp_err & ~data_we_q & lsu_resp_valid_o;
  assign store_err_o     = data_or_pmp_err &  data_we_q & lsu_resp_valid_o;
  // Integrity errors are their own category for timing reasons. load_err_o is factored directly
  // into data_req_o to enable synchronous exception on load errors without performance loss (An
  // upcoming load cannot request until the current load has seen its response, so the earliest
  // point the new request can be sent is the same cycle the response is seen). If load_err_o isn't
  // factored into data_req_o there would have to be a stall cycle between all back to back loads.
  // The data_intg_err signal is generated combinatorially from the incoming data_rdata_i. Were it
  // to be factored into load_err_o there would be a feedthrough path from data_rdata_i to
  // data_req_o which is undesirable.
  assign load_resp_intg_err_o  = data_intg_err & data_rvalid_i & ~data_we_q;
  assign store_resp_intg_err_o = data_intg_err & data_rvalid_i & data_we_q;
endmodule
