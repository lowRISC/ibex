interface core_ibex_reg_file_if #(
    parameter int unsigned DataWidth = 32
  );
  logic                 clk;
  logic                 reset;
  // Read Port 1
  logic [4:0]           raddr_a;
  logic [DataWidth-1:0] rdata_a;
  // Read Port 2
  logic [4:0]           raddr_b;
  logic [DataWidth-1:0] rdata_b;
  // Write Port
  logic [4:0]           waddr_a;
  logic [DataWidth-1:0] wdata_a;
  logic                 we_a;
endinterface
