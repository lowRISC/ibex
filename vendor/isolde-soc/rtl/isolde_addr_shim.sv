// Copyleft ISOLDE


/**

* Validates that addresses fall within the defined range [START_ADDR, END_ADDR].
*   Subtracts START_ADDR from instruction addresses transparently.
*   Passes all other request signals unchanged.
*   Returns memory response directly to the master (CPU).
* Overflow and Underflow Protection:
*    Ensures address translation is safe and doesn’t result in invalid accesses.
* Error Signaling:
*    If an invalid address is detected, the module returns 0xDEADBEEF and sets the error flag in the response.

 */

module isolde_addr_shim #(
    parameter int START_ADDR = 32'h00100000,  // Start address for valid address range
    parameter int END_ADDR   = 32'h00108000   // End address for valid address range
) (
    isolde_tcdm_if.slave  tcdm_slave_i,  // Interface for CPU requests
    isolde_tcdm_if.master tcdm_master_o  // Interface for memory response
);

  // Internal signals for validation
  logic addr_valid;
  logic [31:0] translated_addr;
  isolde_tcdm_if null_dev ();

  // Define a constant invalid response using the type from the interface
  assign null_dev.rsp = '{gnt: 1'b0, valid: 1'b0, data: 32'hDEADBEEF, err: 1'b1};

  // Define a no_request constant to be used when address is invalid
  assign null_dev.req = '{req: 1'b0, we: 1'b0, be: 4'b0000, addr: 32'b0, data: 32'b0};

  // Validate if the address is within the valid range [START_ADDR, END_ADDR]
  assign addr_valid = (tcdm_slave_i.req.addr >= START_ADDR) && (tcdm_slave_i.req.addr <= END_ADDR);

  // Perform address translation only if the address is valid
  assign translated_addr = addr_valid ? (tcdm_slave_i.req.addr - START_ADDR) : 32'hDEADBEEF;  // Invalid address return

  // Single always_comb block for both request forwarding and response handling
  always_comb begin
    if (addr_valid) begin
      // Forward request to slave when address is valid
      tcdm_master_o.req = '{  // Assign each field individually
          req: tcdm_slave_i.req.req,
          we: tcdm_slave_i.req.we,
          be: tcdm_slave_i.req.be,
          addr: translated_addr,  // Assign the translated address
          data: tcdm_slave_i.req.data
      };
      tcdm_slave_i.rsp = tcdm_master_o.rsp;
    end else begin
      // Do not forward request to slave when address is invalid
      tcdm_master_o.req = null_dev.req;

      // Provide invalid response to master when address is invalid
      tcdm_slave_i.rsp  = null_dev.rsp;
    end
  end

endmodule


