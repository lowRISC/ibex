// Copyleft 2025 ISOLDE

module isolde_demux_tcdm #(
    // index type: logic [1:0] 
    //INVALID = rule_idx_t'(2'd0);
    // Address type used in rule struct
    parameter type rule_addr_t = logic,
    // Rule packed struct type. Should follow this format:
    // typedef struct packed {
    //   logic [1:0] idx;
    //   rule_addr_t       start_addr;
    //   rule_addr_t       end_addr;
    // } tb_rule_t;
    parameter type tb_rule_t   = logic,
    parameter bit  rom_memory  = 1

) (
    input logic clk_i,
    input logic rst_ni,
    input tb_rule_t [1:0] mem_map_i,

    input  isolde_tcdm_if.slave  tcdm_slave_i,
    output isolde_tcdm_if.master tcdm_master_o1,
    output isolde_tcdm_if.master tcdm_master_o2
);

  typedef logic [1:0] rule_idx_t;
  localparam rule_idx_t INVALID = rule_idx_t'(2'd0);
  localparam rule_idx_t M_O1 = rule_idx_t'(2'd1);
  localparam rule_idx_t M_O2 = rule_idx_t'(2'd2);
  localparam rule_idx_t LAST_IDX = rule_idx_t'(2'd3);
  localparam int unsigned NoIndices = LAST_IDX;


  logic demux_fifo_full, demux_fifo_empty;
  logic demux_push_id_fifo, demux_pop_id_fifo;
  rule_idx_t demux_selected_idx, demux_rsp_idx;

  assign tcdm_slave_i.rsp.valid = tcdm_master_o2.rsp.valid | tcdm_master_o1.rsp.valid;

  assign demux_push_id_fifo = ~demux_fifo_full & tcdm_slave_i.rsp.gnt;
  assign demux_pop_id_fifo = ~demux_fifo_empty & tcdm_slave_i.rsp.valid;
  //
  logic req_we;
  logic [3:0] req_be;
  logic [31:0] req_data;

  assign req_we   = rom_memory ? 1'b0 : tcdm_slave_i.req.we;
  assign req_be   = rom_memory ? 4'b1111 : tcdm_slave_i.req.be;
  assign req_data = rom_memory ? 32'hABAD_C0DE : tcdm_slave_i.req.data;

  addr_decode #(
      .NoIndices(NoIndices),    // number indices in rules
      .NoRules  (2),            // total number of rules
      .addr_t   (rule_addr_t),  // address type
      .rule_t   (tb_rule_t)     // has to be overridden, see above!
  ) i_addr_decode_rom (
      .addr_i(tcdm_slave_i.req.addr),  // address to decode
      .addr_map_i(mem_map_i),  // address map: rule with the highest position wins
      .idx_o(demux_selected_idx),  // decoded index
      .dec_valid_o(),  // decode is valid
      .dec_error_o(),  // decode is not valid
      // Default index mapping enable
      .en_default_idx_i(1'b1),  // enable default port mapping
      .default_idx_i(INVALID)  // default port index
  );


  // Remember selected master for correct forwarding of read data/acknowledge.
  fifo_v3 #(
      .DATA_WIDTH(4),
      .DEPTH(4)
  ) i_id_fifo_rom (
      .clk_i,
      .rst_ni,
      .flush_i(1'b0),
      .testmode_i(1'b0),
      .full_o(demux_fifo_full),
      .empty_o(demux_fifo_empty),
      .usage_o(),
      // Onehot mask.
      .data_i(demux_selected_idx),
      .push_i(demux_push_id_fifo),
      .data_o(demux_rsp_idx),
      .pop_i(demux_pop_id_fifo)
  );

  always_comb begin : bind_instrs
    tcdm_master_o2.req.req = '0;
    tcdm_master_o1.req.req = '0;
    if (demux_selected_idx == M_O2) begin
      tcdm_master_o2.req.req  = tcdm_slave_i.req.req;
      tcdm_master_o2.req.we   = req_we;
      tcdm_master_o2.req.be   = req_be;
      tcdm_master_o2.req.addr = tcdm_slave_i.req.addr;
      tcdm_master_o2.req.data = req_data;
    end else if (demux_selected_idx == M_O1) begin
      tcdm_master_o1.req.req  = tcdm_slave_i.req.req;
      tcdm_master_o1.req.we   = req_we;
      tcdm_master_o1.req.be   = req_be;
      tcdm_master_o1.req.addr = tcdm_slave_i.req.addr;
      tcdm_master_o1.req.data = req_data;
    end
  end


  always_comb begin
    tcdm_slave_i.rsp.gnt = '0;
    if (tcdm_slave_i.req.req) begin
      case (demux_selected_idx)
        M_O2: tcdm_slave_i.rsp.gnt = tcdm_master_o2.rsp.gnt;
        M_O1: tcdm_slave_i.rsp.gnt = tcdm_master_o1.rsp.gnt;
        default: tcdm_slave_i.rsp.gnt = '0;
      endcase
    end
  end


  always_comb begin
    case (demux_rsp_idx)
      M_O2: tcdm_slave_i.rsp.data = tcdm_master_o2.rsp.data;
      M_O1: tcdm_slave_i.rsp.data = tcdm_master_o1.rsp.data;
      default: tcdm_slave_i.rsp.data = '0;
    endcase
  end

  always_ff @(posedge clk_i, negedge rst_ni)
    if (!rst_ni) begin
      demux_rsp_idx <= INVALID;
    end

endmodule
