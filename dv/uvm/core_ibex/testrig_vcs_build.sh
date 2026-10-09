#!/usr/bin/env bash

# Prototype TestRIG VCS BUILD script
#
# TODO: Replace this script with Makefile rules

export PRJ_DIR=$(realpath ../../../)
export LOWRISC_IP_DIR=$(realpath ${PRJ_DIR}/vendor/lowrisc_ip/)

mkdir -p vcs_testrig_out

vcs \
  -full64 \
  -f ibex_testrig_dv.f \
  -l vcs_testrig_out/compile.log \
  -o vcs_testrig_out/simv \
  -sverilog \
  -ntb_opts uvm-1.2 \
  +define+UVM \
  -licqueue \
  -timescale=1ns/10ps \
  -debug_access+all \
  -CFLAGS "-I${PRJ_DIR}/vendor/socket_packet_utils" \
  -CFLAGS '--std=c99 -fno-extended-identifiers' \
  -LDFLAGS -Wl,--no-as-needed \
  -Xcflags='-Wno-error=implicit-function-declaration -Wno-error=int-conversion'
