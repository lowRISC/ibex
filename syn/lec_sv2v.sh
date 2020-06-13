#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script converts all SystemVerilog RTL files to Verilog
# using sv2v and then runs LEC (Cadence Conformal) to check if
# the generated Verilog is logically equivalent to the original
# SystemVerilog.  This script is similar to:
# https://github.com/lowRISC/opentitan/blob/master/util/syn_yosys.sh
#
# The following tools are required:
#  - sv2v: SystemVerilog-to-Verilog converter from github.com/zachjs/sv2v
#  - Cadence Conformal
#
# Usage:
#   ./lec_sv2v.sh |& tee lec.log

#-------------------------------------------------------------------------
# use fusesoc to generate files and file list
#-------------------------------------------------------------------------
rm -Rf build syn_out
fusesoc --cores-root .. run --tool=icarus --target=lint \
  --setup "lowrisc:ibex:ibex_core" > /dev/null 2>&1

# copy all files to syn_out
mkdir syn_out
cp build/*/src/*/*.sv build/*/src/*/*/*.sv syn_out
cd syn_out

# copy file list and remove incdir, RVFI define, and sim-file
egrep -v 'incdir|RVFI|simulator_ctrl' ../build/*/*/*.scr > flist_gold

# remove all hierarchical paths
sed -i 's!.*/!!' flist_gold

# generate revised flist by replacing '.sv' by '.v' and removing packages
sed 's/.sv/.v/' flist_gold | grep -v "_pkg.v" > flist_rev

#-------------------------------------------------------------------------
# convert all RTL files to Verilog using sv2v
#-------------------------------------------------------------------------
printf "\nSV2V ERRORS:\n"

for file in *.sv; do
  module=`basename -s .sv $file`
  sv2v --define=SYNTHESIS *_pkg.sv prim_assert.sv $file > ${module}.v
done

# TODO: sv2v currently converts '0 to 1'sb0 and '1 to 1'sb1. The latter
# is wrong for multi-bit assignments. And the former causes LEC issues
# if it drives multi-bit inputs (the upper bits of the inputs are undriven)
# convert 1'sb0 to 'd0 and 1'sb1 to -'sd1 (note that -1 is all-ones)
sed -i "s/(1'sb0)/('d0)/" *.v
sed -i "s/(1'sb1)/(-'sd1)/" *.v

# remove *pkg.v files (they are empty files and not needed)
rm -f *_pkg.v prim_assert.v prim_util_memload.v

# overwrite the prim_clock_gating modules with the module from ../rtl
cp ../rtl/prim_clock_gating.v .
cp ../rtl/prim_clock_gating.v prim_clock_gating.sv

#-------------------------------------------------------------------------
# run LEC (generarted Verilog vs. original SystemVerilog)
#-------------------------------------------------------------------------
printf "\n\nLEC RESULTS:\n"

for file in *.v; do
  export LEC_TOP=`basename -s .v $file`

  # special case is file ibex_register_file_ff.sv, whose module has a
  # different name than its file name
  if [[ $LEC_TOP == "ibex_register_file_ff" ]]; then
    export LEC_TOP="ibex_register_file"
  fi

  # run Conformal LEC
  lec -xl -nogui -nobanner \
    -dofile  ../lec_sv2v.do \
    -logfile lec_${LEC_TOP}.log \
    <<< "exit -force" > /dev/null 2>&1

  # summarize results
  check=`grep "Compare Results" lec_${LEC_TOP}.log`
  if [ $? -ne 0 ]; then
    result="CRASH"
  else
    result=`echo $check | awk '{ print $4 }'`
  fi
  printf "%-25s %s\n" $LEC_TOP $result
done
