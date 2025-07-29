`timescale 1ns / 1ps

module tb_isolde_hci_interconnect (
    input logic clk_i,
    input logic rst_ni,
    input logic fetch_enable_i

);

  localparam int unsigned N_TCDM_BANKS = 2;
  localparam int unsigned HCI_DW = N_TCDM_BANKS * 32;





  // DUT connections
  hci_core_intf #(.DW(HCI_DW)) hci_core_hwe (.clk(clk_i));
  isolde_tcdm_if tcdm_core ();

  // === Multi-port Memory  ===

  wire isolde_tcdm_pkg::req_t mem_req[N_TCDM_BANKS:0];
  wire isolde_tcdm_pkg::rsp_t mem_rsp[N_TCDM_BANKS:0];


  // Instantiate multiport memory 
  tb_sram_mem #(
      .ID(0),
      .N_PORTS(N_TCDM_BANKS + 1)
  ) i_sram_mp (
      .clk_i,
      .rst_ni,
      .req_i(mem_req),
      .rsp_o(mem_rsp)
  );


  //DUT
  isolde_hci_interconnect #(
      .HCI_DW(HCI_DW)
  ) dut (
      .clk_i,
      .rst_ni,
      .s_hci_core (hci_core_hwe),
      .s_tcdm_core(tcdm_core),
      .mem_req_o  (mem_req),
      .mem_rsp_i  (mem_rsp)
  );

  task automatic hci_core_transaction(input logic [31:0] addr, input logic [HCI_DW-1:0] data,
                                      output logic [HCI_DW-1:0] r_data, input logic write_enable);
    begin
      hci_core_hwe.req  = 1;
      hci_core_hwe.wen  = write_enable ? 0 : 1;
      hci_core_hwe.be   = write_enable ? 8'hFF : 8'h00;
      hci_core_hwe.add  = addr;
      hci_core_hwe.data = data;
      do @(posedge clk_i); while (!hci_core_hwe.gnt);
      hci_core_hwe.req = 0;
      hci_core_hwe.wen = 1;
      hci_core_hwe.be  = 8'h00;
      //repeat (3) @(posedge clk_i);
      wait (hci_core_hwe.r_valid);
      r_data = hci_core_hwe.r_data;
      @(posedge clk_i);
    end
  endtask

  task automatic tcdm_core_transaction(input logic [31:0] addr, input logic [31:0] data,
                                       output logic [31:0] r_data, input logic write_enable);
    begin
      tcdm_core.req.req  = 1;
      tcdm_core.req.we   = write_enable;
      tcdm_core.req.be   = write_enable ? 4'b1111 : 4'b0000;
      tcdm_core.req.addr = addr;
      tcdm_core.req.data = data;
      do @(posedge clk_i); while (!tcdm_core.rsp.gnt);
      tcdm_core.req.req = 0;
      tcdm_core.req.we  = 0;
      tcdm_core.req.be  = 4'b0000;
      wait (tcdm_core.rsp.valid);
      //do @(posedge clk_i); while (!tcdm_core.rsp.valid);
      r_data = tcdm_core.rsp.data;
    end
  endtask

  // Read task with check
  task automatic check_r_wide_data(input logic [HCI_DW-1:0] actual,
                                   input logic [HCI_DW-1:0] expected);

    begin

      if (actual !== expected) begin
        $error("[Time %0t] ❌ mismatch, expected %h, got %h", $time, expected, actual);
      end else begin
        $display(" check_r_wide_data ✅ ");
      end
    end
  endtask

  // Read task with check
  task automatic read_and_check(input logic [31:0] addr, input logic [31:0] expected);
    logic [31:0] read_data;
    begin
      tcdm_core_transaction(addr, 32'h0BAD_F00D, read_data, 1'b0);  // Read request
      if (read_data !== expected) begin
        $error("[Time %0t] ❌ Read mismatch at address %h: expected %h, got %h", $time, addr,
               expected, read_data);
      end else begin
        $display("[Time %0t] ✅ Read success at address %h: value = %h", $time, addr, read_data);
      end
    end
  endtask

  task automatic write(input logic [31:0] addr, input logic [31:0] wdata);
    logic [31:0] read_data;
    begin
      tcdm_core_transaction(addr, wdata, read_data, 1'b1);  // write request
      if (read_data !== wdata) begin
        $error("[Time %0t] ❌ Write failed at address %h: expected %h, got %h", $time, addr,
               wdata, read_data);
      end else begin
        $display("[Time %0t] ✅ Write success at address %h: value = %h", $time, addr, wdata);
      end
    end
  endtask


  logic [31:0] test_addrs[4] = '{32'h0000_0000, 32'h0000_0004, 32'h0000_0008, 32'h0000_000c};


  logic [31:0] test_data[4] = '{32'hDEAD_BEEF, 32'hCAFE_F00D, 32'hCAFE_DEEA, 32'h1234_5678};
  //
  logic [HCI_DW-1:0] r_wide_data;
  // Input signal generation
  //https://github.com/verilator/verilator/issues/5210
  //*
  //if you need <= assignment in initial block, change the block into allways, otherways it will be treated as =, blocking assigment.
  //*
  // === Test sequence ===
  initial begin
    $readmemh("tb/ab.hex", tb_isolde_hci_interconnect.i_sram_mp.memory);



    // Wait for fetch_enable_i  
    wait (fetch_enable_i);
    @(posedge clk_i);
    //read preloaded values
    read_and_check(32'h0000_0000, 32'hAA_AA_AA_AA);
    read_and_check(32'h0000_0004, 32'hBB_BB_BB_BB);
    read_and_check(32'h0000_0008, 32'hAB_AA_AA_AA);
    //write & read
    foreach (test_addrs[i]) begin
      write(test_addrs[i], test_data[i]);  // Write request
      read_and_check(test_addrs[i], test_data[i]);
    end

    //
    hci_core_transaction(32'h0000_0000, 64'hDEAD_BEEF_FACE_00FF, r_wide_data,
                         1'b0);  // read request
    check_r_wide_data(r_wide_data, {test_data[1], test_data[0]});
    hci_core_transaction(32'h0000_0008, 64'hDEAD_BEEF_FACE_00FF, r_wide_data,
                         1'b0);  // read request
    check_r_wide_data(r_wide_data, {test_data[3], test_data[2]});
    hci_core_transaction(32'h0000_0010, 64'hDEAD_BEEF_FACE_00FF, r_wide_data,
                         1'b0);  // read request
    check_r_wide_data(r_wide_data, 64'hCACA_C0DE_00BE_E000);

    //
    hci_core_transaction(32'h0000_0018, 64'hF00D_BEEF_0BAD_0FEE, r_wide_data,
                         1'b1);  // write request
    check_r_wide_data(r_wide_data, 64'hF00D_BEEF_0BAD_0FEE);
    hci_core_transaction(32'h0000_0018, 64'hDEAD_BEEF_FACE_00FF, r_wide_data,
                         1'b0);  // read request
    check_r_wide_data(r_wide_data, 64'hF00D_BEEF_0BAD_0FEE);
    //
    read_and_check(32'h0000_0018, 32'h0BAD_0FEE);
    read_and_check(32'h0000_001C, 32'hF00D_BEEF);
    //   // === End test ===
    @(posedge clk_i);
    $display("[Time %0t] ✅ Test complete", $time);
    $finish;
  end
endmodule
