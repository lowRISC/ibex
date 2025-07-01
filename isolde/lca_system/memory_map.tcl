# Load the VCD file


# Select the relevant signals
gtkwave::addSignalsFromList {

TOP.clk_i
TOP.rst_ni
TOP.tb_lca_system.i_perfcnt.tcdm_slave_i.rsp[34:0]
TOP.tb_lca_system.i_perfcnt.tcdm_slave_i.req[69:0]
TOP.tb_lca_system.i_perfcnt.tcdm_slave_i.req[69:69]
TOP.tb_lca_system.i_perfcnt.tcdm_slave_i.req[68:68]
TOP.tb_lca_system.i_perfcnt.tcdm_slave_i.req[63:32]
TOP.tb_lca_system.i_perfcnt.tcdm_slave_i.req[31:0]
}