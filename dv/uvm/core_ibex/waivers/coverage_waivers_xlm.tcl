# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Exclude standard primitives that are verified elsewhere
exclude -type "prim_lfsr"
exclude -type "prim_prince"

# Exclude code coverage from aux code used for gathering functional coverage
exclude -type "core_ibex_fcov_if" -metrics code:statement:fsm:assertion
exclude -type "core_ibex_pmp_fcov_if" -metrics code:statement:fsm:assertion

# RVFI signals not present in real design so not relevant to coverage closure
exclude -type "ibex_top" -toggle "rvfi*"
# hart_id_i and boot_addr_i are intended to be hard-wired inputs that do not
# toggle
exclude -type "ibex_top" -toggle "hart_id_i"
exclude -type "ibex_top" -toggle "boot_addr_i"
# ram_cfg_i is a passthrough set of signals to provide memory instance specific
# data and have no functional impact on the design
exclude -type "ibex_top" -toggle "ram_cfg_i.*"
