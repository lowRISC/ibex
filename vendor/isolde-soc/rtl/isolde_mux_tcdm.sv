// Copyleft 2025 ISOLDE

module isolde_mux_tcdm (
    input logic                 clk_i,          // Clock input, positive edge triggered
    input logic                 rst_ni,         // Asynchronous reset, active low
            // Input1 
            input isolde_tcdm_pkg::req_t req_1_i,
            output isolde_tcdm_pkg::rsp_t rsp_1_o,
            // Input2 higher priority
            input isolde_tcdm_pkg::req_t req_2_i,
            output isolde_tcdm_pkg::rsp_t rsp_2_o,
          isolde_tcdm_if.master tcdm_master_o   // Output

);

  logic [1:0] slv_req, slv_rsp;
  assign slv_req[0] = req_1_i.req;
  assign slv_req[1] = req_2_i.req;

  fifo_v3 #(
      .DATA_WIDTH(2),
      .DEPTH(4)
  ) i_slv_fifo (
      .clk_i,
      .rst_ni,
      .flush_i(1'b0),
      .testmode_i(1'b0),
      .full_o(),
      .empty_o(),
      .usage_o(),
      // Onehot mask.
      .data_i(slv_req),
      .push_i(tcdm_master_o.rsp.gnt),
      .data_o(slv_rsp),
      .pop_i(tcdm_master_o.rsp.valid)
  );

  always_comb begin
    tcdm_master_o.req.req = 1'b0;
    if (slv_req[1]) begin
      tcdm_master_o.req.req  = 1'b1;
      tcdm_master_o.req.addr = req_2_i.addr;
      tcdm_master_o.req.we   = req_2_i.we;
      tcdm_master_o.req.be   = req_2_i.be;
      tcdm_master_o.req.data = req_2_i.data;

    end else if (slv_req[0]) begin
      tcdm_master_o.req.req  = 1'b1;
      tcdm_master_o.req.addr = req_1_i.addr;
      tcdm_master_o.req.we   = req_1_i.we;
      tcdm_master_o.req.be   = req_1_i.be;
      tcdm_master_o.req.data = req_1_i.data;
    end
  end


  always_comb begin
    rsp_1_o.gnt = '0;
    rsp_2_o.gnt = '0;
    if (slv_req[1]) begin
      rsp_2_o.gnt = tcdm_master_o.rsp.gnt;
    end else if (slv_req[0]) begin
      rsp_1_o.gnt = tcdm_master_o.rsp.gnt;
    end
  end

  always_comb begin
    rsp_1_o.valid = '0;
    rsp_2_o.valid = '0;
    rsp_1_o.data  = 32'hDEADBEAF;
    rsp_2_o.data  = 32'hDEADBEAF;
    if (slv_rsp[1]) begin
      rsp_2_o.valid = tcdm_master_o.rsp.valid;
      rsp_2_o.data  = tcdm_master_o.rsp.data;
    end else if (slv_rsp[0]) begin
      rsp_1_o.valid = tcdm_master_o.rsp.valid;
      rsp_1_o.data  = tcdm_master_o.rsp.data;
    end
  end


  always_ff @(posedge clk_i or negedge rst_ni) if (~rst_ni) slv_rsp <= '0;
endmodule
