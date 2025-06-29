// Copyleft 2024

// Macro to generate read port signals for a given CHANNEL
`define GEN_X_RF_READ_PORT(CHANNEL) \
  logic [RegAddrWidth-1:0] raddr_``CHANNEL;    /* Read address */ \
  logic [RegDataWidth-1:0] rdata_``CHANNEL;    /* Read data output */

// Interface definition
interface isolde_x_register_file_if #(
    parameter int unsigned RegDataWidth = 32,  // Default register data width
    parameter int unsigned RegAddrWidth = 5    // Default register address width
);

  // Generate four read ports using the macro
  `GEN_X_RF_READ_PORT(0)
  `GEN_X_RF_READ_PORT(1)
  `GEN_X_RF_READ_PORT(2)
  `GEN_X_RF_READ_PORT(3)
  

  // Write port W1
  logic [RegAddrWidth-1:0] waddr_0;  // Write address
  logic [RegDataWidth-1:0] wdata_0;  // Write data
  logic we_0;  // Write enable signal

  // Error detection
  logic isolde_x_rf_err;  // Combined error signal for spurious writes or invalid reads

endinterface


