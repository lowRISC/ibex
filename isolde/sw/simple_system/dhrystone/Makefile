# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generate a baremetal application

# Name of the program $(PROGRAM).c will be added as a source file
PROGRAM = dhrystone
PROGRAM_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
# Any extra source files to include in the build. Use the upper case .S
# extension for assembly files
EXTRA_SRCS :=

# Check the COMPILER variable passed via the command line
ifeq ($(COMPILER), llvm)
    include $(PROGRAM_DIR)/../bsp/common-llvm.mk
else
    include $(PROGRAM_DIR)/../bsp/common.mk
endif

