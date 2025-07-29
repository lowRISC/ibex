`timescale 1ns / 1ps

module tb_isolde_log_interconnect (
    input logic clk_i,
    input logic rst_ni,
    input logic fetch_enable_i

);

  localparam int unsigned N_CORES = 1;
  localparam int unsigned N_TCDM_BANKS = 2;




  // DUT connections
  isolde_tcdm_pkg::req_t cores_req[N_CORES-1:0];
  isolde_tcdm_pkg::rsp_t cores_rsp[N_CORES-1:0];
  isolde_tcdm_pkg::req_t mems_req[N_TCDM_BANKS-1:0];
  isolde_tcdm_pkg::rsp_t mems_rsp[N_TCDM_BANKS-1:0];




  // === Memory banks ===
  generate
    for (genvar i = 0; i < N_TCDM_BANKS; i++) begin : gen_mem
      tb_sram_mem #(
          .ID(i)
      ) i_bank (
          .clk_i,
          .rst_ni,
          .req_i(mems_req[i]),
          .rsp_o(mems_rsp[i])
      );
    end
  endgenerate


  //DUT
  isolde_log_interconnect #(
      .N_SLAVES (N_CORES),
      .N_MASTERS(N_TCDM_BANKS)
  ) dut (
      .clk_i,
      .rst_ni,
      .cores_req_i(cores_req),
      .cores_rsp_o(cores_rsp),
      .mems_req_o (mems_req),
      .mems_rsp_i (mems_rsp)
  );


  task automatic core_req(int unsigned core_id, input logic [31:0] addr, input logic [31:0] data,
                          input logic write_enable);
    begin
      cores_req[core_id].req  = 1;
      cores_req[core_id].we   = write_enable;
      cores_req[core_id].be   = write_enable ? 4'b1111 : 4'b0000;
      cores_req[core_id].addr = addr;
      cores_req[core_id].data = data;
      @(posedge clk_i);
      cores_req[core_id].req = 0;
      cores_req[core_id].we  = 0;
      cores_req[core_id].be  = 4'b0000;
      wait (cores_rsp[core_id].valid);
    end
  endtask

  // Read task with check
  task automatic read_and_check(int unsigned core_id, input logic [31:0] addr,
                                input logic [31:0] expected);
    logic [31:0] read_data;
    begin
      core_req(core_id, addr, 32'h0BAD_F00D, 1'b0);  // Read request
      read_data = cores_rsp[core_id].data;

      if (read_data !== expected) begin
        $error("[Time %0t] ❌ Read mismatch at address %h: expected %h, got %h", $time, addr,
               expected, read_data);
      end else begin
        $display("[Time %0t] ✅ Read success at address %h: value = %h", $time, addr, read_data);
      end
    end
  endtask



  logic [31:0] test_addrs[4] = '{32'h0000_000C, 32'h0000_0010, 32'h0000_0014, 32'h0000_0018};


  logic [31:0] test_data [4] = '{32'hDEAD_BEEF, 32'hCAFE_F00D, 32'hCAFE_DEEA, 32'h1234_5678};
  // Input signal generation
  //https://github.com/verilator/verilator/issues/5210
  //*
  //if you need <= assignment in initial block, change the block into allways, otherways it will be treated as =, blocking assigment.
  //*
  // === Test sequence ===
  initial begin
    $readmemh("tb/a.hex", tb_isolde_log_interconnect.gen_mem[0].i_bank.memory);
    $readmemh("tb/b.hex", tb_isolde_log_interconnect.gen_mem[1].i_bank.memory);


    // Wait for fetch_enable_i  
    wait (fetch_enable_i);
    @(posedge clk_i);
    //read preloaded values
    read_and_check(0, 32'h00000000, 32'hAA_AA_AA_AA);
    read_and_check(0, 32'h00000004, 32'hBB_BB_BB_BB);
    read_and_check(0, 32'h00000008, 32'hAB_AA_AA_AA);
    //write & read
    foreach (test_addrs[i]) begin
      core_req(0, test_addrs[i], test_data[i], 1'b1);  // Write request
      read_and_check(0, test_addrs[i], test_data[i]);
    end

    //   // === End test ===
    @(posedge clk_i);
    $display("[Time %0t] ✅ Test complete", $time);
    $finish;
  end
endmodule
