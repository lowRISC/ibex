module tb_isolde_addr_shim (
    input logic clk_i,
    input logic rst_ni,
    input logic fetch_enable_i

);


  // Instantiate the interface
  isolde_tcdm_if master_if ();
  isolde_tcdm_if slave_if ();

  // Instantiate the shim with START_ADDR and END_ADDR parameters
  isolde_addr_shim #(
      .START_ADDR(32'h80),   // Set start address
      .END_ADDR  (32'hFF00)  // Set end address
  ) dut (
      .tcdm_slave_i(master_if),
      .tcdm_master_o (slave_if)
  );

  initial begin
    $display("Starting Test...");

    // Test Case 1: Valid address (within range)
    master_if.req.addr = 32'h100;  // Address between START_ADDR and END_ADDR
    slave_if.rsp.data  = 32'h100;
    #10;
    $display("Address: %h, Translated: %h, Error: %b, r_data: %h", master_if.req.addr,
             slave_if.req.addr, master_if.rsp.err, master_if.rsp.data);

    // Test Case 2: Address exactly at START_ADDR
    master_if.req.addr = 32'h80;  // Address = START_ADDR
    slave_if.rsp.data  = 32'h200;
    #10;
    $display("Address: %h, Translated: %h, Error: %b, r_data: %h", master_if.req.addr,
             slave_if.req.addr, master_if.rsp.err, master_if.rsp.data);

    // Test Case 3: Address exactly at END_ADDR
    master_if.req.addr = 32'hFF00;  // Address = END_ADDR
    slave_if.rsp.data  = 32'h300;
    #10;
    $display("Address: %h, Translated: %h, Error: %b, r_data: %h", master_if.req.addr,
             slave_if.req.addr, master_if.rsp.err, master_if.rsp.data);

    // Test Case 4: Invalid address (below START_ADDR)
    master_if.req.addr = 32'h40;  // Address < START_ADDR
    slave_if.rsp.data  = 32'h400;
    #10;
    $display("Address: %h, Translated: %h, Error: %b, r_data: %h", master_if.req.addr,
             slave_if.req.addr, master_if.rsp.err, master_if.rsp.data);

    // Test Case 5: Invalid address (above END_ADDR)
    master_if.req.addr = 32'hFF01;  // Address > END_ADDR
    slave_if.rsp.data  = 32'h500;
    #10;
    $display("Address: %h, Translated: %h, Error: %b, r_data: %h", master_if.req.addr,
             slave_if.req.addr, master_if.rsp.err, master_if.rsp.data);

    $finish;
  end
endmodule
