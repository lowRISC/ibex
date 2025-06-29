`timescale 1ns/1ps

module tb_isolde_mux_tcdm(
    input logic clk_i,
    input logic rst_ni,
    input logic fetch_enable_i

);
  
  // Interfaces
  isolde_tcdm_if tcdm_slave_i1();
  isolde_tcdm_if tcdm_slave_i2();
  isolde_tcdm_if tcdm_master_o();

  // Instantiate DUT
  isolde_mux_tcdm dut (
    .clk_i(clk_i),
    .rst_ni(rst_n),
    .tcdm_slave_i1(tcdm_slave_i1),
    .tcdm_slave_i2(tcdm_slave_i2),
    .tcdm_master_o(tcdm_master_o)
  );

  

  // // Monitor: print output from slaves
  // always @(posedge clk_i) begin
  //   if (tcdm_slave_i1.rsp.valid) begin
      
  //     $display("[Time %0t] 🔁 Slave1 received response: DATA = 0x%08x", $time, tcdm_slave_i1.rsp.data);
  //   end
  //   if (tcdm_slave_i2.rsp.valid) begin
      
  //     $display("[Time %0t] 🔁 Slave2 received response: DATA = 0x%08x", $time, tcdm_slave_i2.rsp.data);
  //   end
  // end

  // Test sequence
initial begin
//always begin
  do @(posedge clk_i); while (!fetch_enable_i);
  $display("[Time %0t]  Starting test...", $time);
    // Clear initial requests
    tcdm_slave_i1.req = '{default: 0};
    tcdm_slave_i2.req = '{default: 0};
    tcdm_master_o.rsp = '{default: 0};

    // === Step 1: Slave 1 makes a request ===
    @(posedge clk_i);
    $display("[Time %0t]  Slave1 sending request", $time);
    tcdm_slave_i1.req.req  = 1;
    tcdm_slave_i1.req.addr = 32'h1000_0000;
    tcdm_slave_i1.req.data = 32'hAAAA_AAAA;
    @(posedge clk_i);
    $display("[Time %0t]  Master grants request", $time);
    tcdm_master_o.rsp.gnt = 1;
    tcdm_slave_i1.req.req  = 0;
    @(posedge clk_i);
    $display("[Time %0t]  Master sends response", $time);
    tcdm_master_o.rsp.valid = 1;
    tcdm_master_o.rsp.data  = 32'hC0DE_FACE;
    @(posedge clk_i);
    tcdm_master_o.rsp.gnt   = 0;
    tcdm_master_o.rsp.valid = 0;
    repeat (5) @(posedge clk_i);
    $display("[Time %0t]  Slave2 sending request", $time);
    tcdm_slave_i2.req.req  = 1;
    tcdm_slave_i2.req.addr = 32'h2000_0000;
    tcdm_slave_i2.req.data = 32'hBBBB_BBBB;
    $display("[Time %0t]  Master grants request", $time);
    tcdm_master_o.rsp.gnt = 1;
    tcdm_slave_i2.req.req  = 0;
    repeat (5) @(posedge clk_i);
    $display("[Time %0t]  Master sends response", $time);
    tcdm_master_o.rsp.valid = 1;
    tcdm_master_o.rsp.data  = 32'h00BA_DCE0;
    @(posedge clk_i);
    tcdm_master_o.rsp.gnt   = 0;
    tcdm_master_o.rsp.valid = 0;

  //   // === Step 3: Simulate Master grant ===
  //  #10
  //   $display("[Time %0t]  Master grants request", $time);
  //   tcdm_master_o.rsp.gnt = 1;

  //  //#10
  //  // tcdm_master_o.rsp.gnt = 0;

  //   // === Step 4: Simulate response from Master ===
  //  #10
  //   $display("[Time %0t]  Master sends response", $time);
  //   tcdm_master_o.rsp.valid = 1;
  //   tcdm_master_o.rsp.data  = 32'h1234_5678;

  //  #10
  //   tcdm_master_o.rsp.valid = 0;

  //   // === End test ===
     @(posedge clk_i);
     $display("[Time %0t] ✅ Test complete", $time);
     $finish;
   
  end


endmodule
