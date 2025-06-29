module isolde_bus_tcdm #(
    parameter int NrDevices    = 1,
    parameter int NrHosts      = 1,
    parameter int DataWidth    = 32,
    parameter int AddressWidth = 32
) (
    input logic clk_i,
    input logic rst_ni,

    // Hosts (Masters)
    isolde_tcdm_if.slave host_if[NrHosts],

    // Devices (Slaves)
    isolde_tcdm_if.master device_if[NrDevices],

    // Device address map using start/end addresses
    input logic [AddressWidth-1:0] cfg_device_addr_start[NrDevices],
    input logic [AddressWidth-1:0] cfg_device_addr_end  [NrDevices]
);



  //
  // Hosts (masters)
  //
  logic                    host_req_req    [NrHosts];
  logic                    host_req_we     [NrHosts];
  logic [ DataWidth/8-1:0] host_req_be     [NrHosts];
  logic [AddressWidth-1:0] host_req_addr   [NrHosts];
  logic [   DataWidth-1:0] host_req_data   [NrHosts];
  //master response
  logic                    host_rsp_gnt    [NrHosts];
  logic                    host_rsp_valid  [NrHosts];
  logic                    host_rsp_err    [NrHosts];
  logic [   DataWidth-1:0] host_rsp_data   [NrHosts];

  //
  // Devices (slaves)
  //
  logic                    device_req_req  [NrHosts];
  logic                    device_req_we   [NrHosts];
  logic [ DataWidth/8-1:0] device_req_be   [NrHosts];
  logic [AddressWidth-1:0] device_req_addr [NrHosts];
  logic [   DataWidth-1:0] device_req_data [NrHosts];
  //device response
  logic                    device_rsp_gnt  [NrHosts];
  logic                    device_rsp_valid[NrHosts];
  logic                    device_rsp_err  [NrHosts];
  logic [   DataWidth-1:0] device_rsp_data [NrHosts];
  ;

  localparam int unsigned NumBitsHostSel = (NrHosts > 1) ? $clog2(NrHosts) : 1;
  localparam int unsigned NumBitsDeviceSel = (NrDevices > 1) ? $clog2(NrDevices) : 1;

  logic host_sel_valid;
  logic device_sel_valid;
  logic decode_err_resp;

  logic [NumBitsHostSel-1:0] host_sel_req, host_sel_resp;
  logic [NumBitsDeviceSel-1:0] device_sel_req, selected_device,device_sel_resp;



  //
  //flatten the array of host_if
  //
  generate
    for (genvar host = 0; host < NrHosts; host++) begin : gen_hosts_if
      assign host_req_req[host]      = host_if[host].req.req;
      assign host_req_addr[host]     = host_if[host].req.addr;
      assign host_req_we[host]       = host_if[host].req.we;
      assign host_req_be[host]       = host_if[host].req.be;
      assign host_req_data[host]     = host_if[host].req.data;
      //
      assign host_if[host].rsp.gnt   = host_rsp_gnt[host];
      assign host_if[host].rsp.valid = host_rsp_valid[host];
      assign host_if[host].rsp.data  = host_rsp_data[host];
      assign host_if[host].rsp.err   = host_rsp_err[host];

    end
  endgenerate
  //
  //flatten the array of device_if
  //
  generate
    for (genvar dev = 0; dev < NrDevices; dev++) begin : gen_devices_if
      //req
      assign device_if[dev].req.req  = device_req_req[dev];
      assign device_if[dev].req.addr = device_req_addr[dev];
      assign device_if[dev].req.we   = device_req_we[dev];
      assign device_if[dev].req.be   = device_req_be[dev];
      assign device_if[dev].req.data = device_req_data[dev];
      //rsp
      // assign device_if[dev].rsp.gnt 
      assign device_rsp_gnt[dev]     = device_if[dev].rsp.gnt;
      assign device_rsp_valid[dev]   = device_if[dev].rsp.valid;
      assign device_rsp_err[dev]     = device_if[dev].rsp.err;
      assign device_rsp_data[dev]    = device_if[dev].rsp.data;

    end
  endgenerate

  // Master select prio arbiter
  always_comb begin
    // host_sel_valid = 1'b0;
    host_sel_req   = '0;
    // for (integer host = NrHosts - 1; host >= 0; host = host - 1) begin
    //   if (host_req_i[host]) begin
    host_sel_valid = 1'b1;
    //     host_sel_req   = NumBitsHostSel'(host);
    //   end
    // end
  end

  // Device select
  always_comb begin
    device_sel_valid = 1'b0;
    device_sel_req   = '0;
    for (integer device = 0; device < NrDevices; device = device + 1) begin
      if ((host_req_addr[host_sel_req] >=  cfg_device_addr_start [device])&&
            (host_req_addr[host_sel_req] <   cfg_device_addr_end [device]))  begin
        device_sel_valid = 1'b1;
        device_sel_req   = NumBitsDeviceSel'(device);
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      host_sel_resp   <= '0;
      device_sel_resp <= '0;
      decode_err_resp <= 1'b0;
    end else begin
      // Responses are always expected 1 cycle after the request
      selected_device <= device_sel_req;
      host_sel_resp   <= host_sel_req;
      // Decode failed; no device matched?
      decode_err_resp <= host_sel_valid & !device_sel_valid;
    end
  end

  always_comb begin
    for (integer device = 0; device < NrDevices; device = device + 1) begin
      if (device_sel_valid && NumBitsDeviceSel'(device) == device_sel_req) begin
        device_req_req[device_sel_req]  = host_req_req[host_sel_req];
        device_req_we[device_sel_req]   = host_req_we[host_sel_req];
        device_req_be[device_sel_req]   = host_req_be[host_sel_req];
        device_req_addr[device_sel_req] = host_req_addr[host_sel_req];
        device_req_data[device_sel_req] = host_req_data[host_sel_req];

      end else begin
        device_req_req[device]  = 1'b0;
        device_req_we[device]   = 1'b0;
        device_req_be[device]   = 'b0;
        device_req_addr[device] = 'b0;
        device_req_data[device] = 'b0;
      end
    end
  end

  //always_comb begin
  always_ff @(posedge clk_i or negedge rst_ni) begin
    //  for (integer host = 0; host < NrHosts; host = host + 1) begin

    //     if (NumBitsHostSel'(host) == host_sel_resp) begin
    host_rsp_gnt[host_sel_resp]   <= device_rsp_gnt[device_sel_resp];
    host_rsp_valid[host_sel_resp] <= device_rsp_valid[device_sel_resp];
    host_rsp_err[host_sel_resp]   <= device_rsp_err[device_sel_resp];
    host_rsp_data[host_sel_resp]  <= device_rsp_data[device_sel_resp];
    //    end else begin
    //   host_rsp_gnt[host]   = 1'b0;
    //   host_rsp_valid[host] = 1'b0;
    //   host_rsp_err[host]   = 1'b0;
    //   host_rsp_data[host]  = 'b0;
    // end
    // end

  end

endmodule
