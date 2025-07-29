// Copyleft ISOLDE 2025

/* 
 *
 * 
 */

package isolde_tcdm_pkg;
  localparam int unsigned CORE_DW = 32;  // Data width of CORE interface
  localparam int unsigned CORE_AW = 32;  // Address width of CORE interface
  localparam int unsigned TCDM_AW = 10;  // Address width of TCDM interface
  localparam int unsigned CORE_BEW = 4;  // Byte enable width of CORE interface
  localparam int unsigned ISOLDE_CORE_REQ_SIZE = 1+1+CORE_BEW+CORE_AW+CORE_DW;  // Size of CORE request
  localparam int unsigned ISOLDE_CORE_RSP_SIZE = 1 + 1 + 1 + CORE_DW;  // Size of CORE response

  typedef struct packed {
    logic                req;
    logic                we;
    logic [CORE_BEW-1:0] be;
    logic [CORE_AW-1:0]  addr;
    logic [CORE_DW-1:0]  data;
  } req_t;

  // RESPONSE CHANNEL
  typedef struct packed {
    logic               gnt;
    logic               valid;
    logic               err;
    logic [CORE_DW-1:0] data;
  } rsp_t;

  typedef logic [ISOLDE_CORE_REQ_SIZE-1:0] opaq_req_t;
  typedef logic [ISOLDE_CORE_RSP_SIZE-1:0] opaq_rsp_t;

  function automatic opaq_req_t to_opaq_req(req_t req);
    return opaq_req_t'(req);  // Bit-cast
  endfunction

  function automatic opaq_rsp_t to_opaq_rsp(rsp_t rsp);
    return opaq_rsp_t'(rsp);
  endfunction

  //
  function automatic req_t from_opaq_req(opaq_req_t opaq);
    return req_t'(opaq);
  endfunction

  function automatic rsp_t from_opaq_rsp(opaq_rsp_t opaq);
    return rsp_t'(opaq);
  endfunction


  localparam int unsigned RuleAddrWidth = 32;
  typedef logic [RuleAddrWidth-1:0] rule_addr_t;


  typedef struct packed {
    rule_addr_t start_addr;
    rule_addr_t end_addr;
  } addr_range_t;


endpackage
