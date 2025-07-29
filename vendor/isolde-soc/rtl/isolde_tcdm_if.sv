
// Copyleft 2025 ISOLDE

interface isolde_tcdm_if;



  isolde_tcdm_pkg::req_t req;
  isolde_tcdm_pkg::rsp_t rsp;
  // Master Side
  //***************************************
  modport master(output req, input rsp);

  // Slave Side
  //***************************************
  modport slave(input req, output rsp);

endinterface  // isolde_tcdm_if
