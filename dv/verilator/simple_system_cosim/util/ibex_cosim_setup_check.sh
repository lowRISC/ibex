#!/bin/sh

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

if [[ ! -v IBEX_COSIM_ISS_ROOT ]]; then
  echo "IBEX_COSIM_ISS_ROOT must be set to the root directory of a suitable" \
       "modified spike implementation, see" \
       "dv/verilator/simple_system_cosim/README.md for more details"
  exit 1;
fi

