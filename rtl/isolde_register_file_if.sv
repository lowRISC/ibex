// Copyleft 2024

// Macro to generate read port signals for a given CHANNEL
`define GEN_READ_PORT(CHANNEL) \
  logic [RegAddrWidth-1:0] raddr_``CHANNEL ;                  /* Read address */ \
  logic [RegSize-1:0][RegDataWidth-1:0] rdata_``CHANNEL;      /* Read data output */

// Interface definition
interface isolde_register_file_if;
  import isolde_register_file_pkg::*;

  // Generate two read ports using the macro
  `GEN_READ_PORT(0)
  `GEN_READ_PORT(1)
  `GEN_READ_PORT(2)
  `GEN_READ_PORT(3)

  // Write port W1
  logic [RegAddrWidth-1:0] waddr_0;  // Write address
  logic [RegSize-1:0][RegDataWidth-1:0] wdata_0;  // Write data
  logic [RegSize-1:0][RegDataWidth-1:0] echo_0;  // Echo write data
  logic we_0;  // Write enable signal

  // Error detection
  logic isolde_rf_err;  // Combined error signal for spurious writes or invalid reads

endinterface

