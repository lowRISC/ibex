
// Copyleft 2025 ISOLDE

interface isolde_tcdm_if;

  // REQUEST CHANNEL
  //***************************************
  typedef struct packed {
    logic        req;
    logic        we;
    logic [3:0]  be;
    logic [31:0] addr;
    logic [31:0] data;
  } tcdm_req_t;

  // RESPONSE CHANNEL
  typedef struct packed {
    logic        gnt;
    logic        valid;
    logic        err;
    logic [31:0] data;
  } tcdm_rsp_t;

  tcdm_req_t req;
  tcdm_rsp_t rsp;
  // Master Side
  //***************************************
  modport master(output req, input rsp);

  // Slave Side
  //***************************************
  modport slave(input req, output rsp);

endinterface  // isolde_tcdm_if
