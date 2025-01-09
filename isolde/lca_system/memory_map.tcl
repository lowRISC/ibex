# Load the VCD file


# Select the relevant signals
gtkwave::addSignalsFromList {

TOP.clk_i
TOP.rst_ni
TOP.fetch_enable_i

TOP.tb_lca_system.core_data_req[31:0]
TOP.tb_lca_system.core_data_req[63:32]
TOP.tb_lca_system.core_data_req[67:64]
TOP.tb_lca_system.core_data_req[68:68]
TOP.tb_lca_system.core_data_req[69:69]

TOP.tb_lca_system.mmio_rvalid
TOP.tb_lca_system.cycle_counter
TOP.tb_lca_system.mmio_rdata

TOP.tb_lca_system.core_data_rsp[31:0]
TOP.tb_lca_system.core_data_rsp[32:32]
TOP.tb_lca_system.core_data_rsp[33:33]


TOP.tb_lca_system.core_sleep

TOP.tb_lca_system.redmule_busy
TOP.tb_lca_system.mmio_rvalid
TOP.tb_lca_system.cycle_counter[31:0]
TOP.tb_lca_system.mmio_rdata[31:0]
}