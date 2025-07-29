// Copyleft 2024 ISOLDE

module isolde_router
//import isolde_tcdm_pkg::*;
#(
    parameter int N_RULES = -1,
    parameter isolde_tcdm_pkg::addr_range_t ADDR_RANGES[N_RULES]

) (
    input logic clk_i,
    input logic rst_ni,
    input isolde_tcdm_if.slave tcdm_slave_i,
    output isolde_tcdm_pkg::req_t req_o[N_RULES],
    input isolde_tcdm_pkg::rsp_t rsp_i[N_RULES]

);


  localparam int unsigned IDXWidth = $clog2(N_RULES + 2);  // +2 for INVALID and LAST_IDX
  typedef logic [IDXWidth-1:0] rule_idx_t;
  localparam rule_idx_t INVALID = rule_idx_t'(0);

  typedef struct packed {
    rule_idx_t idx;
    isolde_tcdm_pkg::rule_addr_t start_addr;
    isolde_tcdm_pkg::rule_addr_t end_addr;
  } tb_rule_t;

  localparam tb_rule_t [0:N_RULES-1] addr_map = gen_addr_map(ADDR_RANGES);
  localparam rule_idx_t LAST_IDX = addr_map[N_RULES-1].idx+1;  // Last index is the next after the last rule index
  localparam int unsigned NoIndices = LAST_IDX;




  /*
*  Converts from 0-based index to 1-based index 
*/
  function automatic rule_idx_t mk_one_based_index(rule_idx_t i);
    return (i + 1);
  endfunction

  function automatic tb_rule_t [0:N_RULES-1] gen_addr_map(
      input isolde_tcdm_pkg::addr_range_t ranges[N_RULES]);
    tb_rule_t [0:N_RULES-1] result;
    for (int i = 0; i < N_RULES; i++) begin
      result[i].idx        = mk_one_based_index(i);
      result[i].start_addr = ranges[i].start_addr;
      result[i].end_addr   = ranges[i].end_addr;
    end
    return result;
  endfunction


  // Response valid is OR of all submodule valids
  logic [N_RULES-1:0] rsp_valid_vec;
  logic [N_RULES-1:0] rsp_gnt_vec;


  generate
    for (genvar i = 0; i < N_RULES; i++) begin
      assign rsp_valid_vec[i] = rsp_i[i].valid;
      assign rsp_gnt_vec[i]   = rsp_i[i].gnt;
    end
  endgenerate

  logic fifo_full, fifo_empty;
  logic push_id_fifo, pop_id_fifo;
  rule_idx_t selected_idx, req_idx, rsp_idx;


  assign push_id_fifo = |rsp_gnt_vec;
  assign pop_id_fifo  = |rsp_valid_vec;

  always_ff @(posedge clk_i, negedge rst_ni)
    if (!rst_ni) begin
      rsp_idx <= INVALID;
    end


  addr_decode #(
      .NoIndices(NoIndices),                     // number indices in rules
      .NoRules  (N_RULES),                       // total number of rules
      .addr_t   (isolde_tcdm_pkg::rule_addr_t),  // address type
      .rule_t   (tb_rule_t)                      // has to be overridden, see above!
  ) i_addr_decode_dut (
      .addr_i(tcdm_slave_i.req.addr),  // address to decode
      .addr_map_i(addr_map),  // address map: rule with the highest position wins
      .idx_o(selected_idx),  // decoded index
      .dec_valid_o(),  // decode is valid
      .dec_error_o(),  // decode is not valid
      // Default index mapping enable
      .en_default_idx_i(1'b1),  // enable default port mapping
      .default_idx_i(INVALID)  // default port index
  );

  // Remember selected master for correct forwarding of read data/acknowledge.
  fifo_v3 #(
      .DATA_WIDTH(IDXWidth),
      .DEPTH(4)
  ) i_id_fifo (
      .clk_i,
      .rst_ni,
      .flush_i(1'b0),
      .testmode_i(1'b0),
      .full_o(fifo_full),
      .empty_o(fifo_empty),
      .usage_o(),
      // Onehot mask.
      .data_i(selected_idx),
      .push_i(push_id_fifo),
      .data_o(rsp_idx),
      .pop_i(pop_id_fifo)
  );


  assign req_idx = selected_idx;


  always_comb begin : bind_req
    for (int i = 0; i < N_RULES; i++) begin
      req_o[i] = '0;
      if (req_idx == mk_one_based_index(i)) begin
        req_o[i] = tcdm_slave_i.req;
      end
    end
    //end
  end


  always_comb begin

    tcdm_slave_i.rsp.gnt   = |rsp_gnt_vec;
    tcdm_slave_i.rsp.valid = |rsp_valid_vec;
    tcdm_slave_i.rsp.err   = '0;
    tcdm_slave_i.rsp.data  = '0;
    for (int i = 0; i < N_RULES; i++) begin
      if (req_idx == mk_one_based_index(i)) begin
        tcdm_slave_i.rsp.data = rsp_i[i].data;
      end
    end
  end




  // Compile-time assertion of N_RULES > 0
  // Excluded from synthesis 
`ifndef SYNTHESIS
  initial begin
    assert (N_RULES > 0)
    else $fatal("[isolde_demux_tcdm] ERROR: N_RULES parameter must be > 0 (got %0d)", N_RULES);
  end
`endif
endmodule

