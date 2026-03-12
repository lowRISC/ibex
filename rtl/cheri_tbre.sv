// Copyright Microsoft Corporation
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


module cheri_tbre #(
  parameter int unsigned FifoSize  = 4,      // must be power-of-2
  parameter int unsigned AddrHi    = 31,
  parameter int unsigned DataWidth = 33      // legal values: 32, 33, 65
) (
   // Clock and Reset
  input  logic          clk_i,
  input  logic          rst_ni,

  // MMIO register interface 
  input  logic [65:0]   tbre_ctrl_vec_i,
  output logic          tbre_stat_o,
  output logic          tbre_err_o,

  // LSU req/resp interface (to be multiplixed/qualified)
  input  logic          lsu_tbre_resp_valid_i,
  input  logic          lsu_tbre_resp_err_i,
  input  logic          lsu_tbre_resp_is_wr_i,
  input  logic [DataWidth-1:0] lsu_tbre_raw_rdata_i,   
  input  logic          lsu_tbre_req_done_i,   
  input  logic          lsu_tbre_addr_incr_i,
  output logic          tbre_lsu_req_o,
  output logic          tbre_lsu_is_cap_o,
  output logic          tbre_lsu_we_o,
  output logic [31:0]   tbre_lsu_addr_o,
  output logic [DataWidth-1:0] tbre_lsu_raw_wdata_o,

  // LSU snoop interface
  input  logic          snoop_lsu_req_done_i,   
  input  logic          snoop_lsu_req_i,
  input  logic          snoop_lsu_is_cap_i,
  input  logic          snoop_lsu_we_i,
  input  logic          snoop_lsu_cheri_err_i,
  input  logic [31:0]   snoop_lsu_addr_i,

  // trvk interface
  input  logic          trvk_en_i,
  input  logic          trvk_clrtag_i
);

  localparam bit Mem65Bit = (DataWidth == 65);

  localparam FifoPtrW  = $clog2(FifoSize);
  localparam CapFifoDW = DataWidth+1;
  localparam ReqFifoDW = AddrHi-1;


  logic        tbre_go;
  logic        tbre_add1wait;
  logic        load_stop_cond, load_gnt;
  logic        store_gnt;
  logic        store_req_valid;
  logic [31:0] load_addr, store_addr;
  logic        wait_resp_q;

  logic        req_fifo_wr_en, cap_fifo_wr_en, shdw_fifo_wr_en, fifo_rd_en;

  logic [AddrHi-3:0]     cur_load_addr8, load_addr8_p1;
  logic [FifoPtrW:0]     req_fifo_ext_wr_ptr, cap_fifo_ext_wr_ptr, shdw_fifo_ext_wr_ptr;
  logic [FifoPtrW:0]     os_req_cnt;
  logic [FifoPtrW:0]     fifo_ext_rd_ptr;    
  logic [FifoPtrW-1:0]   req_fifo_wr_ptr, cap_fifo_wr_ptr, shdw_fifo_wr_ptr;
  logic [FifoPtrW-1:0]   fifo_rd_ptr;    
  logic                  shdw_fifo_wr_data;
  logic [CapFifoDW-1:0]  cap_fifo_wr_data;
  logic [ReqFifoDW-1:0]  req_fifo_wr_data;
  logic                  fifo_rd_shdw, fifo_rd_tag, fifo_rd_valid, fifo_rd_err;
  logic [DataWidth-2:0]  fifo_rd_data;
  logic [AddrHi-3:0]     fifo_rd_addr8;
  logic                  fifo_not_empty;
  

  typedef enum logic [1:0] {TBRE_IDLE, TBRE_LOAD, TBRE_WAIT} tbre_fsm_t;
  tbre_fsm_t tbre_fsm_q, tbre_fsm_d;

  typedef enum logic [1:0] {SCH_NONE, SCH_LOAD, SCH_STORE} tbre_sch_t;
  tbre_sch_t tbre_sch_q, tbre_sch_d;

  typedef struct packed {
    logic         go;
    logic         add1wait;
    logic [31:0]  start_addr;
    logic [31:0]  end_addr;
  } tbre_ctrl_t;

  tbre_ctrl_t tbre_ctrl;

  // register interface
  assign tbre_ctrl.go         = tbre_ctrl_vec_i[64];
  assign tbre_ctrl.add1wait   = tbre_ctrl_vec_i[65];
  assign tbre_ctrl.start_addr = tbre_ctrl_vec_i[31:0];
  assign tbre_ctrl.end_addr   = tbre_ctrl_vec_i[63:32];
  assign tbre_stat_o          = (tbre_fsm_q != TBRE_IDLE);

  //  note having resp_valid here improves performance but making timing a bit worse 
  //     (data_rvalid --> tbre_lsu_req --> core/tbre mux select --> data_wdata_o
  assign tbre_lsu_req_o    = ((tbre_sch_q == SCH_LOAD) | ((tbre_sch_q == SCH_STORE) && store_req_valid)) & (~wait_resp_q |  (lsu_tbre_resp_valid_i & ~tbre_ctrl.add1wait));
  assign tbre_lsu_is_cap_o = Mem65Bit ? 1'b1 : (tbre_sch_q == SCH_LOAD);
  assign tbre_lsu_we_o     = (tbre_sch_q == SCH_STORE);
  assign tbre_lsu_addr_o   = (tbre_sch_q == SCH_LOAD) ? load_addr + {lsu_tbre_addr_incr_i, 2'b00} : store_addr;
  assign tbre_lsu_raw_wdata_o  = {1'b0, fifo_rd_data};
         
  assign load_addr8_p1     = cur_load_addr8 + 1;

  assign load_stop_cond  = (load_addr8_p1 > tbre_ctrl.end_addr[AddrHi:3]);
  assign load_gnt        = (tbre_sch_q == SCH_LOAD) & lsu_tbre_req_done_i;
  assign store_gnt       = (tbre_sch_q == SCH_STORE) & lsu_tbre_req_done_i;

  // expand load/store address by concatnating the MSB from start_address (save some area)
  assign load_addr       = (AddrHi >= 31) ? {cur_load_addr8, 3'b000} : 
                           {tbre_ctrl.start_addr[31:AddrHi+1], cur_load_addr8, 3'b000}; 
  assign store_addr      = (AddrHi >= 31) ? {fifo_rd_addr8, 3'b000} : 
                           {tbre_ctrl.start_addr[31:AddrHi+1], fifo_rd_addr8, 3'b000}; 

  always_comb begin
    logic load_stall, req_fifo_full;

    // state machine tracking the progress of memory walk
    if ((tbre_fsm_q == TBRE_IDLE) && tbre_ctrl.go)
      tbre_fsm_d = TBRE_LOAD;
    else if ((tbre_fsm_q == TBRE_LOAD) && load_gnt & load_stop_cond)
      tbre_fsm_d = TBRE_WAIT;
    else if ((tbre_fsm_q == TBRE_WAIT) &&  (os_req_cnt == 0))
      tbre_fsm_d = TBRE_IDLE;
    else
      tbre_fsm_d = tbre_fsm_q;

    // arbitration between load/store requests, throttle if too many outstanding load requests
    //   TBRE assumes a non-buffered memory model (new req won't be gnt'd if the prev response
    //   still outstanding). If not, we have to change this to throttle on resp as well since
    //   the load_store_unit can't handle multiple outstanding requests.
 
    load_stall    = (os_req_cnt >= FifoSize-1);
    req_fifo_full = (os_req_cnt >= FifoSize);

    tbre_sch_d = tbre_sch_q;   // default
    case (tbre_sch_q) 
      SCH_NONE: 
        if ((tbre_fsm_q == TBRE_LOAD) && !req_fifo_full)
          tbre_sch_d = SCH_LOAD;
        else if (store_req_valid)
          tbre_sch_d = SCH_STORE;
      SCH_LOAD:
        if (load_gnt & (load_stall || (tbre_fsm_d == TBRE_WAIT)) & store_req_valid)
          tbre_sch_d = SCH_STORE;
        else if (load_gnt & (load_stall || (tbre_fsm_d == TBRE_WAIT)))
          tbre_sch_d = SCH_NONE;
      SCH_STORE:
        if ((store_gnt | ~store_req_valid) & (tbre_fsm_q == TBRE_LOAD))
          tbre_sch_d = SCH_LOAD;     // no need to check req_fifo_full, since we are dequeing from it
        else if (store_gnt|~store_req_valid)    // go back to NONE to allow reading fifo further
          tbre_sch_d = SCH_NONE;     // no bandwidth loss here since the load req will move ahead anyway
      default:;
    endcase
  end
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tbre_fsm_q      <= TBRE_IDLE;
      tbre_sch_q      <= SCH_NONE;
      cur_load_addr8  <= 'h0;
      wait_resp_q     <= 1'b0;
      tbre_err_o      <= 1'b0;
    end else begin

      tbre_fsm_q <= tbre_fsm_d;
      tbre_sch_q <= tbre_sch_d;

      if (tbre_ctrl.go & (tbre_fsm_q == TBRE_IDLE))
        cur_load_addr8 <= tbre_ctrl.start_addr[AddrHi:3];
      else if (load_gnt)
        cur_load_addr8 <= load_addr8_p1;

      if (load_gnt | store_gnt)
        wait_resp_q <= 1'b1;
      else if (lsu_tbre_resp_valid_i)
        wait_resp_q <= 1'b0;

      // for now just capture/latch errors and flag it to firmware
      if ((tbre_fsm_q == TBRE_IDLE) && tbre_ctrl.go)
        tbre_err_o <= 1'b0;
      else if (lsu_tbre_resp_valid_i && lsu_tbre_resp_err_i)
        tbre_err_o <= 1'b1;
    end
  end

  // FIFOs to buffer caps read from the data memory and shadow bits from the shadow map

  // count of outstand load requests in the pipeline
  assign os_req_cnt = req_fifo_ext_wr_ptr - fifo_ext_rd_ptr;

  assign req_fifo_wr_ptr  = req_fifo_ext_wr_ptr[FifoPtrW-1:0];
  assign cap_fifo_wr_ptr  = cap_fifo_ext_wr_ptr[FifoPtrW-1:0];
  assign shdw_fifo_wr_ptr = shdw_fifo_ext_wr_ptr[FifoPtrW-1:0];
  assign fifo_rd_ptr      = fifo_ext_rd_ptr[FifoPtrW-1:0];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fifo_ext_rd_ptr      <= 'h0;
      req_fifo_ext_wr_ptr  <= 'h0;
      cap_fifo_ext_wr_ptr  <= 'h0;
      shdw_fifo_ext_wr_ptr <= 'h0;
    end else begin
      // FIFO size is power-of-2
      if (fifo_rd_en) fifo_ext_rd_ptr <= fifo_ext_rd_ptr + 1;

      if (req_fifo_wr_en)  req_fifo_ext_wr_ptr  <= req_fifo_ext_wr_ptr + 1;
      if (cap_fifo_wr_en)  cap_fifo_ext_wr_ptr  <= cap_fifo_ext_wr_ptr + 1;      
      if (shdw_fifo_wr_en) shdw_fifo_ext_wr_ptr <= shdw_fifo_ext_wr_ptr + 1;
    end
  end

  logic [FifoSize-1:0][ReqFifoDW-1:0] req_fifo_mem;          // packed entry: addr, valid, 32-bit data
  logic [FifoSize-1:0][CapFifoDW-1:0] cap_fifo_mem;          // packed entry: addr, valid, 32-bit data
  logic [FifoSize-1:0]                shdw_fifo_mem;         // single shadow bit per entry
  
  for (genvar i= 0; i < FifoSize; i++) begin : gen_fifo_mem
    logic [28:0] req_fifo_item_addr8;
    assign req_fifo_item_addr8 = (AddrHi >= 31) ? req_fifo_mem[i][AddrHi-3:0] : 
                           {tbre_ctrl.start_addr[31:AddrHi+1], req_fifo_mem[i][AddrHi-3:0]}; 
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        req_fifo_mem[i]  <= 0;
        cap_fifo_mem[i]  <= 0;
        shdw_fifo_mem[i] <= 1'b0;
      end else begin
        // monitoring the ongoing writes to LSU to detect collisiona
        // also  what about a collision between write request and head of the FIFO? 
        if (req_fifo_wr_en && (i == req_fifo_wr_ptr)) 
          req_fifo_mem[i] <= req_fifo_wr_data;
        else if ((req_fifo_item_addr8 == snoop_lsu_addr_i[31:3]) && snoop_lsu_req_done_i && snoop_lsu_we_i)
          req_fifo_mem[i] <= req_fifo_mem[i] & {1'b0, {(AddrHi-2){1'b1}}};

        if (cap_fifo_wr_en && (i == cap_fifo_wr_ptr)) cap_fifo_mem[i] <= cap_fifo_wr_data;
        if (shdw_fifo_wr_en && (i == shdw_fifo_wr_ptr)) shdw_fifo_mem[i] <= shdw_fifo_wr_data;
      end
    end  // always
  end  // generate

  // peek into the current FIFO head
  assign fifo_rd_addr8  = req_fifo_mem[fifo_rd_ptr][AddrHi-3:0];
  assign fifo_rd_valid  = req_fifo_mem[fifo_rd_ptr][AddrHi-2];
  assign fifo_rd_data   = cap_fifo_mem[fifo_rd_ptr][DataWidth-2:0];
  assign fifo_rd_tag    = cap_fifo_mem[fifo_rd_ptr][DataWidth-1];
  assign fifo_rd_err    = cap_fifo_mem[fifo_rd_ptr][DataWidth];
  assign fifo_rd_shdw   = shdw_fifo_mem[fifo_rd_ptr];

  // only issue invalidation store requests if
  //   valid cap returned && no write collision on the address && shadow_bit == 1 
  assign store_req_valid = fifo_not_empty & fifo_rd_tag & fifo_rd_shdw & fifo_rd_valid & ~fifo_rd_err;

  assign fifo_not_empty = (req_fifo_ext_wr_ptr  != fifo_ext_rd_ptr) && 
                          (cap_fifo_ext_wr_ptr  != fifo_ext_rd_ptr) &&
                          (shdw_fifo_ext_wr_ptr != fifo_ext_rd_ptr);

  assign fifo_rd_en = fifo_not_empty & (((tbre_sch_q == SCH_STORE) & store_gnt) | ~store_req_valid);

  assign req_fifo_wr_en   = (tbre_sch_q == SCH_LOAD) & load_gnt;
  assign req_fifo_wr_data = {1'b1, cur_load_addr8};

  assign cap_fifo_wr_en   = lsu_tbre_resp_valid_i & ~lsu_tbre_resp_is_wr_i;
  assign cap_fifo_wr_data = {lsu_tbre_resp_err_i, lsu_tbre_raw_rdata_i};

  assign shdw_fifo_wr_en   = trvk_en_i;
  assign shdw_fifo_wr_data = trvk_clrtag_i;
  
endmodule
