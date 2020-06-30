# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A simple wrapper around fusesoc to make it a bit easier to run the formal flow

# Whether to use ECC (0 for disabled; 1 for enabled)
ECC := 0

core-name   := lowrisc:fpv:ibex_icache_fpv
vlnv        := $(subst :,_,$(core-name))
build-root  := $(abspath ../../build/$(vlnv))

fusesoc-params := --ICacheECC=$(ECC)

fusesoc-run := fusesoc --cores-root=../.. run --build-root=$(build-root)

.PHONY: all prove lint
all: prove

prove:
	$(fusesoc-run) $(core-name) $(fusesoc-params)

lint:
	mypy --strict sv2v_in_place.py
