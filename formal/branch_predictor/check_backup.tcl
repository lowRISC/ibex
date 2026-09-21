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

# All paths relative to ibex/formal/branch_predict/ (where JG is invoked).
# RTL lives two levels up in the ibex repo; this check requires the surrounding
# ibex checkout to be present.

# Package first, then the DUT.  prim_assert.sv is pulled in via `include so we
# just need its directory on the search path.
analyze -sv12 \
    +incdir+../../vendor/lowrisc_ip/ip/prim/rtl \
    ../../rtl/ibex_pkg.sv \
    ../../rtl/ibex_branch_predict.sv

# Formal testbench module (assertions + covers)
analyze -sv12 \
    +incdir+../../vendor/lowrisc_ip/ip/prim/rtl \
    formal_tb.sv

# Bind formal_tb into ibex_branch_predict via wildcard port connections
analyze -sv12 branch_predict_bind.sv

elaborate -top ibex_branch_predict -disable_auto_bbox

clock clk_i
reset -expression {!rst_ni}

# Force Hp (Heuristic Proof) as the proof engine, running entirely within the
# JG process.  The default prove -all tries to launch a job-dispatch daemon
# (jg_bgd) which fails on this machine with EPF117/EPF044.  Hp is sufficient
# for this combinational module: both assertions are pure combinational
# equalities and all covers are reachable in a single cycle.
prove -all -engine_mode Hp

report -summary
report -file results.txt -force
