// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

module ibex_load_store_unit import ibex_pkg::*; import cheri_pkg::*; #(
  parameter bit          MemECC       = 1'b0,
  parameter int unsigned MemDataWidth = MemECC ? 32 + 7 : 32,
  parameter int unsigned DataWidth    = 33,        // legal values: 32, 33, 65
  parameter bit          CHERIoTEn    = 1'b1,
  parameter bit          MemCapFmt    = 1'b0,
  parameter bit          CheriTBRE    = 1'b0,
  parameter bit          CheriCapIT8  = 1'b0
) (
  input  logic         clk_i,
  input  logic         rst_ni,
  input  logic         cheri_pmode_i,

  // data interface
  output logic         data_req_o,
  output logic         data_is_cap_o,
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
  input  logic         cpu_lsu_we_i,         // write enable                     -> from ID/EX
  input  logic         cpu_lsu_is_cap_i,     // kliu
  input  logic         cpu_lsu_cheri_err_i,  // kliu
  input  logic [1:0]   cpu_lsu_type_i,       // data type: word, half word, byte -> from ID/EX
  input  logic [31:0]  cpu_lsu_wdata_i,      // data to write to memory          -> from ID/EX
  input  reg_cap_t     cpu_lsu_wcap_i,       // kliu
  input  logic [3:0]   cpu_lsu_lc_clrperm_i,
  input  logic         cpu_lsu_sign_ext_i,   // sign extension                   -> from ID/EX

  input  logic         cpu_stall_by_stkz_i,
  input  logic         cpu_grant_to_stkz_i,

  output reg_cap_t     lsu_rcap_o,           // kliu
  output logic [31:0]  lsu_rdata_o,          // requested data                   -> to ID/EX
  output logic         lsu_rdata_valid_o,
  input  logic         cpu_lsu_req_i,        // data request                     -> from ID/EX

  input  logic [31:0]  cpu_lsu_addr_i,       // address computed in ALU          -> from ID/EX

  output logic         lsu_addr_incr_req_o,  // request address increment for
                                              // misaligned accesses              -> to ID/EX
  output logic [31:0]  addr_last_o,          // address of last transaction      -> to controller
                                              // -> mtval
                                              // -> AGU for misaligned accesses

  output logic         lsu_req_done_o,        // Signals that data request is complete
                                              // (only need to await final data
                                              // response)                        -> to ID/EX
  output logic         lsu_resp_valid_o,      // LSU has response from transaction -> to ID/EX & WB
  output logic         lsu_resp_is_wr_o,

  // TBRE related signals
  input  logic         tbre_lsu_req_i,
  input  logic         tbre_lsu_is_cap_i,
  input  logic         tbre_lsu_we_i,
  input  logic [31:0]  tbre_lsu_addr_i,
  input  logic [DataWidth-1:0]  tbre_lsu_raw_wdata_i,
  input  logic         cpu_lsu_dec_i,
  output logic         lsu_tbre_sel_o,
  output logic         lsu_tbre_addr_incr_req_o,  // request address increment for
  output logic [DataWidth-1:0] lsu_tbre_raw_rdata_o,
  output logic         lsu_tbre_req_done_o,
  output logic         lsu_tbre_resp_valid_o, // response from transaction -> to TBRE
  output logic         lsu_tbre_resp_err_o,

  // exception signals
  output logic         load_err_o,
  output logic         load_resp_intg_err_o,
  output logic         store_err_o,
  output logic         store_resp_intg_err_o,
  output logic         lsu_err_is_cheri_o,

  output logic         busy_o,
  output logic         busy_tbre_o,

  output logic         perf_load_o,
  output logic         perf_store_o
);


  localparam bit DataMem65Bit = (DataWidth == 65);

  logic [31:0]  data_addr;
  logic [31:0]  data_addr_w_aligned;
  logic [31:0]  addr_last_q, addr_last_d;

  logic         addr_update;
  logic         ctrl_update;
  logic         rdata_update;
  logic [31:8]  rdata_q;
  logic [1:0]   rdata_offset_q;
  logic [1:0]   data_type_q;
  logic         data_sign_ext_q;
  logic         data_we_q;

  logic [1:0]   data_offset;   // mux control for data to be written to memory

  logic [3:0]   data_be;
  logic [DataWidth-1:0]   data_wdata;

  logic [31:0]  data_rdata_ext;

  logic [31:0]  rdata_w_ext; // word realignment for misaligned loads
  logic [31:0]  rdata_h_ext; // sign extension for half words
  logic [31:0]  rdata_b_ext; // sign extension for bytes

  logic         split_misaligned_access;
  logic         handle_misaligned_q, handle_misaligned_d; // high after receiving grant for first
                                                          // part of a misaligned access
  logic         pmp_err_q, pmp_err_d;
  logic         lsu_err_q, lsu_err_d;
  logic         data_intg_err, data_or_pmp_err;

  logic         resp_is_cap_q;
  logic         cheri_err_d, cheri_err_q;
  logic [3:0]   resp_lc_clrperm_q;
  logic         cur_req_is_tbre;
  logic         req_is_tbre_q;
  logic         resp_is_tbre;
  logic         tbre_req_good;
  logic         outstanding_resp_q, resp_wait;
  logic         lsu_resp_valid;
  logic         lsu_go, lsu_go_goodcap;
  logic         addr_incr_req;
  logic         cpu_req_erred, cpu_req_valid;

  logic         lsu_tbre_sel;
  logic [31:0]  lsu_addr;
  logic         lsu_we;
  logic         lsu_is_cap;
  logic         lsu_cheri_err;
  logic [1:0]   lsu_type;
  logic [32:0]  lsu_wdata33;
  reg_cap_t     lsu_wcap;
  logic [3:0]   lsu_lc_clrperm;
  logic         lsu_sign_ext;


  ls_fsm_e ls_fsm_cs, ls_fsm_ns;

  cap_rx_fsm_t cap_rx_fsm_q, cap_rx_fsm_d;

  logic         cap_lsw_err_q;
  logic [32:0]  cap_lsw_q;

  assign data_addr   = lsu_addr;
  assign data_offset = (cheri_pmode_i & lsu_is_cap) ? 2'b00 : data_addr[1:0];

  // multiplex inputs between CPU and TBRE/stkz
  assign lsu_cheri_err   = ~lsu_tbre_sel ? cpu_lsu_cheri_err_i  : 1'b0;
  assign lsu_we          = ~lsu_tbre_sel ? cpu_lsu_we_i         : tbre_lsu_we_i;
  assign lsu_addr        = ~lsu_tbre_sel ? cpu_lsu_addr_i       : tbre_lsu_addr_i;

  if (DataMem65Bit) begin
    assign lsu_wdata33   = {1'b0, cpu_lsu_wdata_i};    //  tbre wdata mux hanled later (wdata_o)
  end else begin
    assign lsu_wdata33   = ~lsu_tbre_sel ? {cpu_lsu_wcap_i.valid, cpu_lsu_wdata_i} : tbre_lsu_raw_wdata_i;
  end

  assign lsu_is_cap      = ~lsu_tbre_sel ? cpu_lsu_is_cap_i     : tbre_lsu_is_cap_i;
  assign lsu_lc_clrperm  = ~lsu_tbre_sel ? cpu_lsu_lc_clrperm_i : 0;
  assign lsu_type        = ~lsu_tbre_sel ? cpu_lsu_type_i       : 2'b00;
  assign lsu_wcap        = ~lsu_tbre_sel ? cpu_lsu_wcap_i       : NULL_REG_CAP;
  assign lsu_sign_ext    = ~lsu_tbre_sel ? cpu_lsu_sign_ext_i   : 1'b0;

  ///////////////////
  // BE generation //
  ///////////////////

  always_comb begin
    if (CHERIoTEn & cheri_pmode_i & lsu_is_cap)
      data_be = 4'b1111;                  // caps are always word aligned
    else begin
      unique case (lsu_type) // Data type 00 Word, 01 Half word, 11,10 byte
        2'b00: begin // Writing a word
          if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
            unique case (data_offset)
              2'b00:   data_be = 4'b1111;
              2'b01:   data_be = 4'b1110;
              2'b10:   data_be = 4'b1100;
              2'b11:   data_be = 4'b1000;
              default: data_be = 4'b1111;
            endcase // case (data_offset)
          end else begin // second part of misaligned transaction
            unique case (data_offset)
              2'b00:   data_be = 4'b0000; // this is not used, but included for completeness
              2'b01:   data_be = 4'b0001;
              2'b10:   data_be = 4'b0011;
              2'b11:   data_be = 4'b0111;
              default: data_be = 4'b1111;
            endcase // case (data_offset)
          end
        end

        2'b01: begin // Writing a half word
          if (!handle_misaligned_q) begin // first part of potentially misaligned transaction
            unique case (data_offset)
              2'b00:   data_be = 4'b0011;
              2'b01:   data_be = 4'b0110;
              2'b10:   data_be = 4'b1100;
              2'b11:   data_be = 4'b1000;
              default: data_be = 4'b1111;
            endcase // case (data_offset)
          end else begin // second part of misaligned transaction
            data_be = 4'b0001;
          end
        end

        2'b10,
        2'b11: begin // Writing a byte
          unique case (data_offset)
            2'b00:   data_be = 4'b0001;
            2'b01:   data_be = 4'b0010;
            2'b10:   data_be = 4'b0100;
            2'b11:   data_be = 4'b1000;
            default: data_be = 4'b1111;
          endcase // case (data_offset)
        end

        default:     data_be = 4'b1111;
      endcase // case (lsu_type)
    end  // if lsu_cap
  end

  /////////////////////
  // WData alignment //
  /////////////////////

  // prepare data to be written to the memory
  // we handle misaligned accesses, half word and byte accesses here
  logic [32:0] wdata_int;
  always_comb begin
     unique case (data_offset)
       2'b00:   wdata_int = lsu_wdata33[32:0];
       2'b01:   wdata_int = {1'b0, lsu_wdata33[23:0], lsu_wdata33[31:24]};
       2'b10:   wdata_int = {1'b0, lsu_wdata33[15:0], lsu_wdata33[31:16]};
       2'b11:   wdata_int = {1'b0, lsu_wdata33[ 7:0], lsu_wdata33[31: 8]};
       default: wdata_int = lsu_wdata33[32:0];
     endcase // case (data_offset)
   end

  // When in Mem65Bit mode tbre/stkz do a raw 65-bit memcap write (is_cap == 1)
  // When in Mem33Bit mode tbre/stkz do a normal 33-bit integer data write (is_cap == 0)
  if (DataMem65Bit) begin : gen_memcap_wr_65bit
    always_comb begin
      if (CHERIoTEn & cheri_pmode_i & lsu_is_cap & ~lsu_tbre_sel) begin
        data_wdata[DataWidth-1:32] = CheriCapIT8 ? reg2memcap_it8_fmt0(lsu_wcap) :
                                     reg2memcap_fmt0(lsu_wcap);
        data_wdata[31:0] = lsu_wdata33[31:0];
      end else if (CHERIoTEn & cheri_pmode_i & lsu_is_cap) begin
        data_wdata = tbre_lsu_raw_wdata_i;
      end else begin
        data_wdata = {33'h0, wdata_int[31:0]};
      end
    end
  end else if (~MemCapFmt) begin : gen_memcap_wr_fmt0
    always_comb begin
      if (CHERIoTEn & cheri_pmode_i & lsu_is_cap && (ls_fsm_cs == CTX_WAIT_GNT2))
        data_wdata = CheriCapIT8 ? reg2memcap_it8_fmt0(lsu_wcap):
                                   reg2memcap_fmt0(lsu_wcap);
      else if (CHERIoTEn & cheri_pmode_i & lsu_is_cap)
        data_wdata = lsu_wdata33;
      else
        data_wdata = wdata_int;
    end
  end else begin : gen_memcap_wr_fmt1
    logic [65:0] mem_capaddr;
    assign mem_capaddr = CheriCapIT8 ? reg2mem_it8_fmt1(lsu_wcap, lsu_wdata33) :
                                       reg2mem_fmt1(lsu_wcap, lsu_wdata33);

    always_comb begin
      if (CHERIoTEn & lsu_is_cap && (ls_fsm_cs == CTX_WAIT_GNT2))
        data_wdata = mem_capaddr[65:33];
      else if (CHERIoTEn & lsu_is_cap)
        data_wdata = mem_capaddr[32:0];
      else
        data_wdata = wdata_int;
    end
  end
  /////////////////////
  // RData alignment //
  /////////////////////

  // register for unaligned rdata
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_q <= '0;
    end else if (rdata_update) begin
      rdata_q <= data_rdata_i[31:8];
    end
  end

  // registers for transaction control
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_offset_q  <= 2'h0;
      data_type_q     <= 2'h0;
      data_sign_ext_q <= 1'b0;
      data_we_q       <= 1'b0;
    end else if (ctrl_update) begin
      rdata_offset_q  <= data_offset;
      data_type_q     <= lsu_type;
      data_sign_ext_q <= lsu_sign_ext;
      data_we_q       <= lsu_we;
    end
  end

  // Store last address for mtval + AGU for misaligned transactions.  Do not update in case of
  // errors, mtval needs the (first) failing address.  Where an aligned access or the first half of
  // a misaligned access sees an error provide the calculated access address. For the second half of
  // a misaligned access provide the word aligned address of the second half.
  assign addr_last_d = addr_incr_req ? data_addr_w_aligned : data_addr;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_last_q <= '0;
    end else if (addr_update & ~cur_req_is_tbre) begin
      addr_last_q <= addr_last_d;
    end
  end

  // take care of misaligned words
  always_comb begin
    unique case (rdata_offset_q)
      2'b00:   rdata_w_ext = data_rdata_i[31:0];
      2'b01:   rdata_w_ext = {data_rdata_i[ 7:0], rdata_q[31:8]};
      2'b10:   rdata_w_ext = {data_rdata_i[15:0], rdata_q[31:16]};
      2'b11:   rdata_w_ext = {data_rdata_i[23:0], rdata_q[31:24]};
      default: rdata_w_ext = data_rdata_i[31:0];
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

  // SEC_CM: BUS.INTEGRITY
  if (MemECC) begin : g_mem_rdata_ecc
    logic [1:0] ecc_err;
    logic [MemDataWidth-1:0] data_rdata_buf;

    prim_buf #(.Width(MemDataWidth)) u_prim_buf_instr_rdata (
      .in_i (data_rdata_i),
      .out_o(data_rdata_buf)
    );

    prim_secded_inv_39_32_dec u_data_intg_dec (
      .data_i     (data_rdata_buf),
      .data_o     (),
      .syndrome_o (),
      .err_o      (ecc_err)
    );

    // Don't care if error is correctable or not, they're all treated the same
    assign data_intg_err = |ecc_err;
  end else begin : g_no_mem_data_ecc
    assign data_intg_err = 1'b0;
  end

  /////////////
  // LSU FSM //
  /////////////

  // check for misaligned accesses that need to be split into two word-aligned accesses
  assign split_misaligned_access =
      ((lsu_type == 2'b00) && (data_offset != 2'b00)) || // misaligned word access
      ((lsu_type == 2'b01) && (data_offset == 2'b11));   // misaligned half-word access

  assign cpu_req_valid = cpu_lsu_req_i & ~lsu_cheri_err & ~cpu_stall_by_stkz_i;
  assign cpu_req_erred = cpu_lsu_req_i & lsu_cheri_err;

  // FSM
  always_comb begin
    ls_fsm_ns       = ls_fsm_cs;

    data_req_o          = 1'b0;
    addr_incr_req     = 1'b0;
    handle_misaligned_d = handle_misaligned_q;
    pmp_err_d           = pmp_err_q;
    lsu_err_d           = lsu_err_q;
    cheri_err_d         = cheri_err_q & cheri_pmode_i;

    addr_update         = 1'b0;
    ctrl_update         = 1'b0;
    rdata_update        = 1'b0;

    perf_load_o         = 1'b0;
    perf_store_o        = 1'b0;

    lsu_go              = 1'b0;
    lsu_go_goodcap      = 1'b0;

    unique case (ls_fsm_cs)

      IDLE: begin
        pmp_err_d   = 1'b0;
        cheri_err_d = 1'b0;

        if (CHERIoTEn & cheri_pmode_i & cpu_req_erred & ~resp_wait) begin
          // cheri access error case, don't issue data_req but send error response back to WB stage
          data_req_o   = 1'b0;
          cheri_err_d  = 1'b1;
          ctrl_update  = 1'b1;         // update ctrl/address so we can report error correctly
          addr_update  = 1'b1;
          pmp_err_d    = 1'b0;
          lsu_err_d    = 1'b0;
          perf_load_o  = 1'b0;
          lsu_go       = 1'b1;         // decision to move forward with a request
          ls_fsm_ns    = IDLE;
        end else if (CHERIoTEn & cheri_pmode_i & (cpu_req_valid | tbre_req_good) &
                     lsu_is_cap & ~resp_wait) begin
          // normal cap access case
          data_req_o   = 1'b1;
          cheri_err_d  = 1'b0;
          pmp_err_d    = data_pmp_err_i;
          lsu_err_d    = 1'b0;
          perf_load_o  = ~lsu_we;
          perf_store_o = lsu_we;
          lsu_go       = 1'b1;         // decision to move forward with a request
          lsu_go_goodcap = 1'b1;

          if (DataMem65Bit && data_gnt_i) begin
            ctrl_update         = 1'b1;
            addr_update         = 1'b1;
            ls_fsm_ns           = IDLE;
          end else if (DataMem65Bit) begin
            ls_fsm_ns           = CTX_WAIT_GNT2;
          end else if (data_gnt_i) begin
            ctrl_update         = 1'b1;
            addr_update         = 1'b1;
            ls_fsm_ns           = CTX_WAIT_GNT2;
          end else begin
            ls_fsm_ns           = CTX_WAIT_GNT1;
          end
        end else if ((cpu_req_valid | tbre_req_good) & ~resp_wait) begin
          // normal data access case
          data_req_o   = 1'b1;
          cheri_err_d  = 1'b0;
          pmp_err_d    = data_pmp_err_i;
          lsu_err_d    = 1'b0;
          perf_load_o  = ~lsu_we;
          perf_store_o = lsu_we;
          lsu_go       = 1'b1;         // decision to move forward with a request

          if (data_gnt_i) begin
            ctrl_update         = 1'b1;
            addr_update         = 1'b1;
            handle_misaligned_d = split_misaligned_access;
            ls_fsm_ns           = split_misaligned_access ? WAIT_RVALID_MIS : IDLE;
          end else begin
            ls_fsm_ns           = split_misaligned_access ? WAIT_GNT_MIS    : WAIT_GNT;
          end
        end

      end

      WAIT_GNT_MIS: begin
        data_req_o = 1'b1;
        // data_pmp_err_i is valid during the address phase of a request. An error will block the
        // external request and so a data_gnt_i might never be signalled. The registered version
        // pmp_err_q is only updated for new address phases and so can be used in WAIT_GNT* and
        // WAIT_RVALID* states
        if (data_gnt_i || pmp_err_q ) begin
          addr_update         = 1'b1;
          ctrl_update         = 1'b1;
          handle_misaligned_d = 1'b1;
          ls_fsm_ns           = WAIT_RVALID_MIS;
        end
      end

      WAIT_RVALID_MIS: begin
        // push out second request
        data_req_o = 1'b1;
        // tell ID/EX stage to update the address
        addr_incr_req = 1'b1;

        // first part rvalid is received, or gets a PMP error
        if (data_rvalid_i || pmp_err_q) begin
          // Update the PMP error for the second part
          pmp_err_d = data_pmp_err_i;
          // Record the error status of the first part
          lsu_err_d = data_bus_err_i | pmp_err_q;
          // Capture the first rdata for loads
          rdata_update = ~data_we_q;
          // If already granted, wait for second rvalid
          ls_fsm_ns = data_gnt_i ? IDLE : WAIT_GNT;
          // Update the address for the second part, if no error
          addr_update = data_gnt_i & ~(data_bus_err_i | pmp_err_q);
          // clear handle_misaligned if second request is granted
          handle_misaligned_d = ~data_gnt_i;
        end else begin
          // first part rvalid is NOT received
          if (data_gnt_i) begin
            // second grant is received
            ls_fsm_ns = WAIT_RVALID_MIS_GNTS_DONE;
            handle_misaligned_d = 1'b0;
          end
        end
      end

      WAIT_GNT: begin
        // tell ID/EX stage to update the address
        addr_incr_req = handle_misaligned_q;
        data_req_o      = 1'b1;
        if (data_gnt_i || pmp_err_q) begin
          ctrl_update         = 1'b1;
          // Update the address, unless there was an error
          addr_update         = ~lsu_err_q;
          ls_fsm_ns           = IDLE;
          handle_misaligned_d = 1'b0;
        end
      end

      WAIT_RVALID_MIS_GNTS_DONE: begin
        // tell ID/EX stage to update the address (to make sure the
        // second address can be captured correctly for mtval and PMP checking)
        addr_incr_req = 1'b1;
        // Wait for the first rvalid, second request is already granted
        if (data_rvalid_i) begin
          // Update the pmp error for the second part
          pmp_err_d = data_pmp_err_i ;
          // The first part cannot see a PMP error in this state
          lsu_err_d = data_bus_err_i;
          // Now we can update the address for the second part if no error
          addr_update = ~data_bus_err_i;
          // Capture the first rdata for loads
          rdata_update = ~data_we_q;
          // Wait for second rvalid
          ls_fsm_ns = IDLE;
        end
      end

      CTX_WAIT_GNT1: begin
        if (cheri_pmode_i) begin
          addr_incr_req = 1'b0;
          data_req_o    = 1'b1;
          if (data_gnt_i) begin
            ls_fsm_ns = CTX_WAIT_GNT2;
            ctrl_update         = 1'b1;
            addr_update         = 1'b1;
           end
        end else begin
          ls_fsm_ns = IDLE;
        end
      end

      CTX_WAIT_GNT2: begin
        if (cheri_pmode_i) begin
          addr_incr_req = ~DataMem65Bit;
          data_req_o    = 1'b1;
          if (data_gnt_i && (data_rvalid_i || (cap_rx_fsm_q == CRX_WAIT_RESP2))) ls_fsm_ns = IDLE;
          else if (data_gnt_i) ls_fsm_ns = CTX_WAIT_RESP;

          if (DataMem65Bit && data_gnt_i) begin
            ctrl_update         = 1'b1;
            addr_update         = 1'b1;
          end
        end else begin
          ls_fsm_ns = IDLE;
        end
      end

      CTX_WAIT_RESP: begin        // only needed if mem allows 2 active req
        if (cheri_pmode_i) begin
          addr_incr_req = ~DataMem65Bit;  // if 33-bit memory, stay 1 to reduce unnecessary addr toggling
          data_req_o    = 1'b0;
          if (data_rvalid_i) ls_fsm_ns = IDLE;
        end else begin
          ls_fsm_ns = IDLE;
        end
      end

      default: begin
        ls_fsm_ns = IDLE;
      end
    endcase
  end

  always_comb begin
    cap_rx_fsm_d = cap_rx_fsm_q;

    case (cap_rx_fsm_q)
      CRX_IDLE:
        if (CHERIoTEn & DataMem65Bit & cheri_pmode_i & lsu_go_goodcap)
          cap_rx_fsm_d = CRX_WAIT_RESP2;
        //else if (CHERIoTEn & cheri_pmode_i & lsu_is_cap && (ls_fsm_ns != IDLE))
        else if (CHERIoTEn & cheri_pmode_i & lsu_go_goodcap)
          cap_rx_fsm_d = CRX_WAIT_RESP1;
      CRX_WAIT_RESP1:
        if (data_rvalid_i) cap_rx_fsm_d = CRX_WAIT_RESP2;
      CRX_WAIT_RESP2:
        if (DataMem65Bit & data_rvalid_i && lsu_go_goodcap)
          cap_rx_fsm_d = CRX_WAIT_RESP2;
        //else if (data_rvalid_i && lsu_is_cap && (ls_fsm_ns != IDLE))
        else if (data_rvalid_i && lsu_go_goodcap)
          cap_rx_fsm_d = CRX_WAIT_RESP1;
        else if (data_rvalid_i) cap_rx_fsm_d = CRX_IDLE;
      default:;
    endcase
  end

  // this is the decision of granting LSU to TBRE/STKZ
  assign tbre_req_good  = CHERIoTEn & cheri_pmode_i & CheriTBRE & tbre_lsu_req_i &
                          (~cpu_lsu_dec_i | (cpu_lsu_dec_i & cpu_grant_to_stkz_i));

  assign resp_wait = CHERIoTEn & cheri_pmode_i & CheriTBRE & outstanding_resp_q & ~lsu_resp_valid;

  // we assume ctrl will be held till req_done asserted
  // (once req captured in IDLE, it can be deasserted)
  logic lsu_req_done;

  assign lsu_req_done        = (lsu_go | (ls_fsm_cs != IDLE)) & (ls_fsm_ns == IDLE);

  assign lsu_req_done_o      = lsu_req_done & (~cur_req_is_tbre);
  assign lsu_tbre_req_done_o = lsu_req_done & cur_req_is_tbre & cheri_pmode_i;

  assign lsu_addr_incr_req_o      = addr_incr_req & ~cur_req_is_tbre;
  assign lsu_tbre_addr_incr_req_o = addr_incr_req & cur_req_is_tbre;

  assign cur_req_is_tbre = CHERIoTEn & cheri_pmode_i & CheriTBRE & ((ls_fsm_cs == IDLE) ?
                           (tbre_req_good & ~resp_wait) : req_is_tbre_q);

  assign lsu_tbre_sel   = cur_req_is_tbre;      // req ctrl signal mux select (to cheri_ex/tbre_wrapper)
  assign lsu_tbre_sel_o = lsu_tbre_sel;

  // registers for FSM
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ls_fsm_cs           <= IDLE;
      handle_misaligned_q <= '0;
      pmp_err_q           <= '0;
      lsu_err_q           <= '0;
      resp_is_cap_q       <= 1'b0;
      resp_lc_clrperm_q   <= 4'h0;
      req_is_tbre_q       <= 1'b0;
      cheri_err_q         <= 1'b0;
      cap_rx_fsm_q        <= CRX_IDLE;
      cap_lsw_err_q       <= 1'b0;
      cap_lsw_q           <= 33'h0;
      outstanding_resp_q  <= 1'b0;
    end else begin
      ls_fsm_cs           <= ls_fsm_ns;
      handle_misaligned_q <= handle_misaligned_d;
      pmp_err_q           <= pmp_err_d;
      lsu_err_q           <= lsu_err_d;
      cheri_err_q         <= cheri_err_d;

      cap_rx_fsm_q        <= cap_rx_fsm_d;

      // resp_is_cap_q aligns with responses on the data interface, lsu_is_cap aligns with requests
      //   we use lsu_go to qualify this update
      //   - note this implies that LSU only support a outstand request at a time
      //   - new request can't be issued (go) until resp_valid
      //   - also note resp_valid is gated by (ls_fsm_cs == IDLE)
      if (lsu_go) begin
        resp_is_cap_q     <= lsu_is_cap;
        resp_lc_clrperm_q <= lsu_lc_clrperm;
        req_is_tbre_q     <= cur_req_is_tbre;
      end

      if (CHERIoTEn & cheri_pmode_i && (cap_rx_fsm_q == CRX_WAIT_RESP1) && data_rvalid_i && (~data_we_q))
        cap_lsw_q <= data_rdata_i;

      if (CHERIoTEn & cheri_pmode_i && (cap_rx_fsm_q == CRX_WAIT_RESP1) && data_rvalid_i)
        cap_lsw_err_q <= data_err_i;

      if (lsu_go)
        outstanding_resp_q <= 1'b1;
      else if (lsu_resp_valid)
        outstanding_resp_q <= 1'b0;

    end
  end

  /////////////
  // Outputs //
  /////////////

  assign resp_is_tbre = req_is_tbre_q;

  logic all_resp;
  assign data_or_pmp_err    = lsu_err_q | data_bus_err_i | pmp_err_q | (cheri_pmode_i &
                              (cheri_err_q | (resp_is_cap_q & cap_lsw_err_q)));

  assign all_resp           = data_rvalid_i | pmp_err_q | (cheri_pmode_i & cheri_err_q);
  assign lsu_resp_valid     = all_resp & (ls_fsm_cs == IDLE) ;

  assign lsu_resp_valid_o        = lsu_resp_valid & (~cheri_pmode_i | (~resp_is_tbre)) ;
  assign lsu_tbre_resp_valid_o   = lsu_resp_valid & resp_is_tbre;
  assign lsu_resp_is_wr_o        = data_we_q;

  // this goes to wb as rf_we_lsu, so needs to be gated when data needs to go back to EX
  assign lsu_rdata_valid_o  = (ls_fsm_cs == IDLE) & data_rvalid_i & ~data_or_pmp_err & ~data_we_q &
                              (~cheri_pmode_i | (~resp_is_tbre)) & ~data_intg_err;

  // output to register file
  if (CHERIoTEn & DataMem65Bit) begin : gen_memcap_rd_65bit
    logic [32:0] rdata_msw, rdata_lsw;
    assign       rdata_msw = data_rdata_i[DataWidth-1:32];
    assign       rdata_lsw = {data_rdata_i[DataWidth-1], data_rdata_i[31:0]};

    assign lsu_rdata_o = data_rdata_ext;
    assign lsu_rcap_o  = (resp_is_cap_q && data_rvalid_i && (cap_rx_fsm_q == CRX_WAIT_RESP2) && (~data_or_pmp_err)) ?
                         (CheriCapIT8 ? mem2regcap_it8_fmt0(rdata_msw, rdata_lsw, resp_lc_clrperm_q) :
                                        mem2regcap_fmt0(rdata_msw, rdata_lsw, resp_lc_clrperm_q)) : NULL_REG_CAP;

  end else if (CHERIoTEn & ~MemCapFmt) begin : gen_memcap_rd_fmt0
    assign lsu_rdata_o = (cheri_pmode_i & resp_is_cap_q) ? cap_lsw_q[31:0] : data_rdata_ext;
    assign lsu_rcap_o  = (resp_is_cap_q && data_rvalid_i && (cap_rx_fsm_q == CRX_WAIT_RESP2) && (~data_or_pmp_err)) ?
                         (CheriCapIT8 ? mem2regcap_it8_fmt0(data_rdata_i, cap_lsw_q, resp_lc_clrperm_q) :
                                        mem2regcap_fmt0(data_rdata_i, cap_lsw_q, resp_lc_clrperm_q)) : NULL_REG_CAP;
  end else if (CHERIoTEn) begin : gen_memcap_rd_fmt1
    assign lsu_rdata_o = (cheri_pmode_i & resp_is_cap_q) ? mem2regaddr_fmt1(data_rdata_i, cap_lsw_q, lsu_rcap_o): data_rdata_ext;
    assign lsu_rcap_o  = (resp_is_cap_q && data_rvalid_i && (cap_rx_fsm_q == CRX_WAIT_RESP2) && (~data_or_pmp_err)) ?
                         (CheriCapIT8 ?  mem2regcap_it8_fmt1(data_rdata_i, cap_lsw_q, resp_lc_clrperm_q) :
                                         mem2regcap_fmt1(data_rdata_i, cap_lsw_q, resp_lc_clrperm_q)) : NULL_REG_CAP;
  end else begin : gen_no_cap_rd
    assign lsu_rdata_o = data_rdata_ext;
    assign lsu_rcap_o  = NULL_REG_CAP;
  end


  // "raw" memory word to tbre
  assign lsu_tbre_raw_rdata_o = DataMem65Bit ? data_rdata_i : cap_lsw_q;

  // output data address must be word aligned
  assign data_addr_w_aligned = {data_addr[31:2], 2'b00};

  // output to data interface
  assign data_addr_o   = data_addr_w_aligned;
  // output to data interface
  assign data_addr_o   = data_addr_w_aligned;
  assign data_we_o     = lsu_we;
  assign data_be_o     = data_be;

  assign data_is_cap_o = lsu_is_cap;

  /////////////////////////////////////
  // Write data integrity generation //
  /////////////////////////////////////

  // SEC_CM: BUS.INTEGRITY
  if (MemECC) begin : g_mem_wdata_ecc
    prim_secded_inv_39_32_enc u_data_gen (
      .data_i (data_wdata),
      .data_o (data_wdata_o)
    );
  end else begin : g_no_mem_wdata_ecc
    assign data_wdata_o = data_wdata;
  end

  // output to ID stage: mtval + AGU for misaligned transactions
  assign addr_last_o   = addr_last_q;

  // Signal a load or store error depending on the transaction type outstanding
  assign load_err_o    = data_or_pmp_err & ~data_we_q & lsu_resp_valid & (~resp_is_tbre);
  assign store_err_o   = data_or_pmp_err &  data_we_q & lsu_resp_valid & (~resp_is_tbre);

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

  assign busy_o = (ls_fsm_cs != IDLE);

  //////////
  // FCOV //
  //////////
`ifndef DV_FCOV_DISABLE
  // Set when awaiting the response for the second half of a misaligned access
  logic fcov_mis_2_en_d, fcov_mis_2_en_q;

  // fcov_mis_rvalid_1: Set when the response is received to the first half of a misaligned access,
  // fcov_mis_rvalid_2: Set when response is received for the second half
  logic fcov_mis_rvalid_1, fcov_mis_rvalid_2;

  // Set when the first half of a misaligned access saw a bus error
  logic fcov_mis_bus_err_1_d, fcov_mis_bus_err_1_q;

  assign fcov_mis_rvalid_1 = ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_RVALID_MIS_GNTS_DONE} &&
                                data_rvalid_i;

  assign fcov_mis_rvalid_2 = ls_fsm_cs inside {IDLE} && fcov_mis_2_en_q && data_rvalid_i;

  assign fcov_mis_2_en_d = fcov_mis_rvalid_2 ? 1'b0            :  // clr
                           fcov_mis_rvalid_1 ? 1'b1            :  // set
                                               fcov_mis_2_en_q ;

  assign fcov_mis_bus_err_1_d = fcov_mis_rvalid_2                   ? 1'b0                 : // clr
                                fcov_mis_rvalid_1 && data_bus_err_i ? 1'b1                 : // set
                                                                      fcov_mis_bus_err_1_q ;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fcov_mis_2_en_q <= 1'b0;
      fcov_mis_bus_err_1_q <= 1'b0;
    end else begin
      fcov_mis_2_en_q <= fcov_mis_2_en_d;
      fcov_mis_bus_err_1_q <= fcov_mis_bus_err_1_d;
    end
  end
`endif

  `DV_FCOV_SIGNAL(logic, ls_error_exception, (load_err_o | store_err_o) & ~pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_pmp_exception, (load_err_o | store_err_o) & pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_first_req, cpu_lsu_req_i & (ls_fsm_cs == IDLE))
  `DV_FCOV_SIGNAL(logic, ls_second_req,
    (ls_fsm_cs inside {WAIT_RVALID_MIS}) & data_req_o & lsu_addr_incr_req_o)
  `DV_FCOV_SIGNAL(logic, ls_mis_pmp_err_1,
    (ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_GNT_MIS}) && pmp_err_q)
  `DV_FCOV_SIGNAL(logic, ls_mis_pmp_err_2,
    (ls_fsm_cs inside {WAIT_RVALID_MIS, WAIT_RVALID_MIS_GNTS_DONE}) && data_pmp_err_i)

  assign lsu_err_is_cheri_o  = cheri_pmode_i & cheri_err_q;     // send to controller for mcause encoding
  assign lsu_tbre_resp_err_o = cheri_pmode_i & data_or_pmp_err & lsu_resp_valid & resp_is_tbre;

  assign busy_o = (ls_fsm_cs != IDLE);
  // assign busy_tbre_o = (ls_fsm_cs != IDLE) & cur_req_is_tbre;
  assign busy_tbre_o = (ls_fsm_cs != IDLE) & cheri_pmode_i & resp_is_tbre;

endmodule
