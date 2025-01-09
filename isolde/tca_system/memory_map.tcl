# Load the VCD file


# Select the relevant signals
gtkwave::addSignalsFromList {

TOP.clk_i
TOP.rst_ni
TOP.fetch_enable_i

TOP.tb_tca_system.core_data_req[31:0]
TOP.tb_tca_system.core_data_req[63:32]
TOP.tb_tca_system.core_data_req[67:64]
TOP.tb_tca_system.core_data_req[68:68]
TOP.tb_tca_system.core_data_req[69:69]

TOP.tb_tca_system.mmio_rvalid
TOP.tb_tca_system.cycle_counter
TOP.tb_tca_system.mmio_rdata

TOP.tb_tca_system.core_data_rsp[31:0]
TOP.tb_tca_system.core_data_rsp[32:32]
TOP.tb_tca_system.core_data_rsp[33:33]

}


