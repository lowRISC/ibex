#!/usr/bin/env bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script drives the experimental Ibex synthesis flow. More details can be
# found in README.md

set -e
set -o pipefail

error () {
    echo >&2 "$@"
    exit 1
}

teelog () {
    tee "$LR_SYNTH_OUT_DIR/log/$1.log"
}

if [ ! -f syn_setup.sh ]; then
    error "No syn_setup.sh file: see README.md for instructions"
fi

#-------------------------------------------------------------------------
# setup flow variables
#-------------------------------------------------------------------------
source syn_setup.sh

LR_DEP_SOURCES=(
    "../vendor/lowrisc_ip/ip/prim_generic/rtl/prim_generic_buf.sv"
    "../vendor/lowrisc_ip/ip/prim_generic/rtl/prim_generic_flop.sv"
)

mkdir -p "$LR_SYNTH_OUT_DIR/generated"
mkdir -p "$LR_SYNTH_OUT_DIR/log"
mkdir -p "$LR_SYNTH_OUT_DIR/reports/timing"

# remove tracer (not needed for synthesis)
rm -f "$LR_SYNTH_OUT_DIR"/generated/ibex_tracer.v

# remove the FPGA & register-based register file (because we will use the
# latch-based one instead)
rm -f "$LR_SYNTH_OUT_DIR"/generated/ibex_register_file_ff.v
rm -f "$LR_SYNTH_OUT_DIR"/generated/ibex_register_file_fpga.v

yosys -m "$LR_SYNTH_SYNLIG_PLUGIN_PATH" -c ./tcl/yosys_run_synth.tcl |& teelog syn || {
    error "Failed to synthesize RTL with Yosys"
}

sta ./tcl/sta_run_reports.tcl |& teelog sta || {
    error "Failed to run static timing analysis"
}

./translate_timing_rpts.sh

python/get_kge.py "$LR_SYNTH_CELL_LIBRARY_PATH" "$LR_SYNTH_OUT_DIR"/reports/area.rpt
