// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Coverage support is not available in Verilator but it's useful to include extra fcov signals for
// linting purposes. They need to be marked as unused to avoid warnings.

// Include FCOV RTL by default. Exclude it for synthesis and where explicitly requested (by defining
// EXCLUDE_FCOV).
`ifdef SYNTHESIS
  `define EXCLUDE_FCOV
`elsif YOSYS
  `define EXCLUDE_FCOV
`endif

`ifdef VERILATOR
  `define FCOV_MARK_UNUSED(__var_type, __var_name) \
    __var_type unused_fcov_``__var_name; \
    assign unused_fcov_``__var_name = fcov_``__var_name;
`else
  `define FCOV_MARK_UNUSED(__var_type, __var_name)
`endif

`ifndef FCOV_SIGNAL
`define FCOV_SIGNAL(__var_type, __var_name, __var_definition) \
  `ifndef EXCLUDE_FCOV \
    __var_type fcov_``__var_name; \
\
    assign fcov_``__var_name = __var_definition; \
\
    `FCOV_MARK_UNUSED(__var_type, __var_name) \
  `endif
`endif

`ifndef FCOV_SIGNAL_GEN_IF
`define FCOV_SIGNAL_GEN_IF(__var_type, __var_name, __var_definition, __generate_test, __default_val = '0) \
  `ifndef EXCLUDE_FCOV \
    __var_type fcov_``__var_name; \
\
    if (__generate_test) begin : g_fcov_``__var_name \
      assign fcov_``__var_name = __var_definition; \
    end else begin : g_no_fcov_``__var_name \
      assign fcov_``__var_name = __default_val; \
    end \
\
    `FCOV_MARK_UNUSED(__var_type, __var_name) \
  `endif
`endif
