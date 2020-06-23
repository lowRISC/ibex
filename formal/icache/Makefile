# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A simple wrapper around fusesoc to make it a bit easier to run the formal flow

core-name   := lowrisc:fpv:ibex_icache_fpv
vlnv        := $(subst :,_,$(core-name))
build-root  := $(abspath ../../build/$(vlnv))

fusesoc-run := cd ../..; fusesoc --cores-root=. run

.PHONY: all prove lint
all: prove

prove:
	fusesoc --cores-root=../.. run --build-root=$(build-root) $(core-name)

lint:
	mypy --strict sv2v_in_place.py
