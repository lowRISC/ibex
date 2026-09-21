# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Standalone Makefile for the ibex_branch_predict formal check.
# Run from this directory (requires jg on PATH — enter the formal nix shell first):
#   make batch   -- headless JasperGold run, exits 0 on pass
#   make gui     -- open JasperGold GUI
#   make clean   -- remove JasperGold project and log files

JG_FLAGS := -allow_unsupported_OS -proj jgproject -acquire_proj

.PHONY: batch gui clean

batch:
	jg check.tcl $(JG_FLAGS) -no_gui -command exit 2>&1 | tee run.log; exit $${PIPESTATUS[0]}

gui:
	jg check.tcl $(JG_FLAGS)

clean:
	rm -rf jgproject run.log results.txt
