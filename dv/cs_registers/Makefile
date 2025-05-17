# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

TOOL     = verilator

SO_NAME  = reg_dpi.so

BUILDDIR = build
SRCEXT   = cc
OBJDIR   = $(BUILDDIR)/obj
BINDIR   = $(BUILDDIR)/bin

SRCS    := $(shell find . -name '*.$(SRCEXT)' ! -path './tb/*' ! -path './build/*')
SRCDIRS := $(shell find . -name '*.$(SRCEXT)' ! -name 'tb*' ! -name 'build*' -exec dirname {} \; | uniq)
OBJS    := $(patsubst %.$(SRCEXT),$(OBJDIR)/%.o,$(SRCS))

DEBUG    = -g
INCLUDES = -I./env -I./rst_driver -I./reg_driver -I./model
CFLAGS   = -std=c++14 -m64 -fPIC -Wall -pedantic $(DEBUG) $(INCLUDES)
LDFLAGS  = -shared

CC       = $(CXX)

# Add svdpi include
# Check if VERILATOR_ROOT is set, use it first if available
ifdef VERILATOR_ROOT
  VERILATOR_INCLUDE = $(VERILATOR_ROOT)/include
else
  # Try to find Verilator installation directory
  TOOLDIR = $(subst bin/$(TOOL),,$(shell which $(TOOL) 2>/dev/null))
  
  # Define list of possible Verilator include paths to check
  VERILATOR_INCLUDE_PATHS := \
    $(TOOLDIR)share/verilator/include \
    $(TOOLDIR)share/verilator/include/vltstd \
    /usr/share/verilator/include \
    /usr/local/share/verilator/include \
    /opt/verilator/share/verilator/include \
    $(HOME)/verilator/include
    
  # Find first valid include path
  VERILATOR_INCLUDE := $(firstword $(foreach dir,$(VERILATOR_INCLUDE_PATHS),$(if $(wildcard $(dir)/svdpi.h),$(dir),)))
  
  # If include path not found, provide error messages
  ifeq ($(VERILATOR_INCLUDE),)
    $(warning WARNING: Could not find Verilator include directory with svdpi.h)
    $(warning Searched in: $(VERILATOR_INCLUDE_PATHS))
    $(warning You can manually specify it using: make build-csr-test INCLUDES="-I/path/to/verilator/include -I./env -I./rst_driver -I./reg_driver -I./model")
    $(warning Or set VERILATOR_ROOT environment variable pointing to your Verilator installation)
  endif
endif

# Add appropriate includes based on tool
ifeq ($(TOOL),vcs)
  INCLUDES += -I$(TOOLDIR)include
else ifeq ($(TOOL),verilator)
  ifdef VERILATOR_INCLUDE
    INCLUDES += -I$(VERILATOR_INCLUDE) -I$(VERILATOR_INCLUDE)/vltstd
  endif
endif

.PHONY: all clean

all: build

build: $(BINDIR)/$(SO_NAME)
	@echo "Build done"

$(BINDIR)/$(SO_NAME): buildrepo $(OBJS)
	@mkdir -p `dirname $@`
	@echo "Linking $@..."
	@$(CC) $(OBJS) $(LDFLAGS) -o $@

$(OBJDIR)/%.o: %.$(SRCEXT)
	@echo "Generating dependencies for $<..."
	@$(call make-depend,$<,$@,$(subst .o,.d,$@))
	@echo "Compiling $<..."
	@$(CC) $(CFLAGS) -c $< -o $@

clean:
	$(RM) -r $(BUILDDIR)

buildrepo:
	@$(call make-repo)

define make-repo
   for dir in $(SRCDIRS); \
   do \
	mkdir -p $(OBJDIR)/$$dir; \
   done
endef


# usage: $(call make-depend,source-file,object-file,depend-file)
define make-depend
  $(CC) -MM       \
        -MF $3    \
        -MP       \
        -MT $2    \
        $(CFLAGS) \
        $1
endef

