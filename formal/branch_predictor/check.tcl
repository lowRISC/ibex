# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# JasperGold formal check for ibex_branch_predict.
#
# Run via the local Makefile (from this directory):
#   make batch   -- headless run, exits with pass/fail status
#   make gui     -- open JasperGold GUI

clear -all

# RTL: package + module.  prim_assert.sv is pulled in via `include, so we
# only need its directory on the include search path.
analyze -sv12 \
    +incdir+. \
    +incdir+../../vendor/lowrisc_ip/ip/prim/rtl \
    ../../rtl/ibex_pkg.sv \
    ../../rtl/ibex_branch_predict.sv \
    formal_tb.sv \
    branch_predict_bind.sv

elaborate -top ibex_branch_predict -disable_auto_bbox

clock clk_i
reset -expression {!rst_ni}

# Disable the ProofGrid bridge (Advanced Job Dispatch daemon).
# The bridge fails to start on this machine (EPF117/EPF044); disabling it
# lets the Hp engine run proofs locally in-process.
set_proofgrid_bridge off

prove -all -engine_mode Hp

report -summary
report -file results.txt -force
