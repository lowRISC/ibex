# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2025.09
# platform  : Linux 6.18.33
# version   : 2025.09p002 64 bits
# build date: 2025.11.19 14:35:23 UTC
# ----------------------------------------
# started   : 2026-09-21 10:07:03 BST
# hostname  : nyx.(none)
# pid       : 4136455
# arguments : '-style' 'windows' '-label' 'session_0' '-console' '//127.0.0.1:41277' '-nowindow' '-data' 'AAABFnicVY7dCcJAEIS/EwTxQcRHSxC0gvQgYgEhJIcaYy7RE33TUu3knJxgyC77N7M7rAGSVwiBaObzqySGoXXzaIjs3oMK456cKBbkHLHKZzZ41UroijWZugrHg5Q7NTflRu64as9SCN+y1/ZU241QRxkVSw7/uVP2QpdRMaeVykmc1XV/MxNbq0912fEwF5ILucgzcUX81/IU6+P3XzTKJV0=' '-bridge_url' ':-1' '-proj' '/home/evmorfiaa/ibex/formal/tmp_04/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/evmorfiaa/ibex/formal/tmp_04/jgproject/.tmp/.initCmds.tcl' 'check.tcl' '-hidden' '/home/evmorfiaa/ibex/formal/tmp_04/jgproject/.tmp/.postCmds.tcl'
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
exit
