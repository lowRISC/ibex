// Copyleft 2025 ISOLDE

module isolde_mux_tcdm (
    input logic                 clk_i,          // Clock input, positive edge triggered
    input logic                 rst_ni,         // Asynchronous reset, active low
          isolde_tcdm_if.slave  tcdm_slave_i1,  // Input1 
          isolde_tcdm_if.slave  tcdm_slave_i2,  // Input2 higher priority
          isolde_tcdm_if.master tcdm_master_o   // Output

);

  logic [1:0] slv_req, slv_rsp;
  assign slv_req[0] = tcdm_slave_i1.req.req;
  assign slv_req[1] = tcdm_slave_i2.req.req;

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
      tcdm_master_o.req.addr = tcdm_slave_i2.req.addr;
      tcdm_master_o.req.we   = tcdm_slave_i2.req.we;
      tcdm_master_o.req.be   = tcdm_slave_i2.req.be;
      tcdm_master_o.req.data = tcdm_slave_i2.req.data;

    end else if (slv_req[0]) begin
      tcdm_master_o.req.req  = 1'b1;
      tcdm_master_o.req.addr = tcdm_slave_i1.req.addr;
      tcdm_master_o.req.we   = tcdm_slave_i1.req.we;
      tcdm_master_o.req.be   = tcdm_slave_i1.req.be;
      tcdm_master_o.req.data = tcdm_slave_i1.req.data;
    end
  end


  always_comb begin
    tcdm_slave_i1.rsp.gnt = '0;
    tcdm_slave_i2.rsp.gnt = '0;
    if (slv_req[1]) begin
      tcdm_slave_i2.rsp.gnt = tcdm_master_o.rsp.gnt;
    end else if (slv_req[0]) begin
      tcdm_slave_i1.rsp.gnt = tcdm_master_o.rsp.gnt;
    end
  end

  always_comb begin
    tcdm_slave_i1.rsp.valid = '0;
    tcdm_slave_i2.rsp.valid = '0;
    tcdm_slave_i1.rsp.data  = 32'hDEADBEAF;
    tcdm_slave_i2.rsp.data  = 32'hDEADBEAF;
    if (slv_rsp[1]) begin
      tcdm_slave_i2.rsp.valid = tcdm_master_o.rsp.valid;
      tcdm_slave_i2.rsp.data  = tcdm_master_o.rsp.data;
    end else if (slv_rsp[0]) begin
      tcdm_slave_i1.rsp.valid = tcdm_master_o.rsp.valid;
      tcdm_slave_i1.rsp.data  = tcdm_master_o.rsp.data;
    end
  end


  always_ff @(posedge clk_i or negedge rst_ni) if (~rst_ni) slv_rsp <= '0;
endmodule
