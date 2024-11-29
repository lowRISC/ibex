package isolde_cv_x_if_pkg;

  parameter int unsigned X_NUM_RS               = 3;  // Number of register file read ports that can be used by the eXtension interface
  parameter int unsigned X_ID_WIDTH             = 10;  // Width of ID field.
  parameter int unsigned X_RFR_WIDTH            = 32; // Register file read access width for the eXtension interface
  parameter int unsigned X_RFW_WIDTH            = 32; // Register file write access width for the eXtension interface
  parameter int unsigned X_NUM_HARTS            = 1;  // Number of harts (hardware threads) associated with the interface
  parameter int unsigned X_HARTID_WIDTH         = 1;  // Width of ``hartid`` signals.
  parameter logic [25:0] X_MISA                 = '0; // MISA extensions implemented on the eXtension interface
  parameter int unsigned X_DUALREAD             = 0;  // Is dual read supported? 0: No, 1: Yes, for ``rs1``, 2: Yes, for ``rs1`` - ``rs2``, 3: Yes, for ``rs1`` - ``rs3``
  parameter int unsigned X_DUALWRITE            = 0;  // Is dual write supported? 0: No, 1: Yes.
  parameter int unsigned X_ISSUE_REGISTER_SPLIT = 0;  // Does the interface pipeline register interface? 0: No, 1: Yes.
  parameter int unsigned X_MEM_WIDTH            = 32;  // Memory access width for loads/stores via the eXtension interface
  parameter logic [ 1:0] X_ECS_XS               = '0;  // Default value for mstatus.XS
endpackage
