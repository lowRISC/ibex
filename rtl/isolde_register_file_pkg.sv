package isolde_register_file_pkg;

  parameter int unsigned RegDataWidth = 32;  // Width of each data element (default is 32 bits)
  parameter int unsigned RegCount = 15;  // Number of registers (default is 15)
  parameter int unsigned RegSize = 4;  // Number of data words per register (4 words per register)
  //
  parameter int unsigned RegAddrWidth = $clog2(RegCount);  // Address width, automatically calculated
endpackage
