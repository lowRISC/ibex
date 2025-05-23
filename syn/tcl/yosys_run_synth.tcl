# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

source ./tcl/yosys_common.tcl

if { $lr_synth_flatten } {
  set flatten_opt "-flatten"
} else {
  set flatten_opt ""
}

if { $lr_synth_timing_run } {
  write_sdc_out $lr_synth_sdc_file_in $lr_synth_sdc_file_out
}

yosys "read_systemverilog -defer \
  -PSYNTHESIS=true \
  -PYOSYS=true \
  -I../vendor/lowrisc_ip/ip/prim/rtl/ \
  -I../vendor/lowrisc_ip/dv/sv/dv_utils \
  rtl/prim_clock_gating.v \
  rtl/prim_buf.sv \
  rtl/prim_flop.sv \
  ../vendor/lowrisc_ip/ip/prim_generic/rtl/prim_generic_buf.sv \
  ../vendor/lowrisc_ip/ip/prim_generic/rtl/prim_generic_flop.sv \
  ../rtl/ibex_pkg.sv \
  ../vendor/lowrisc_ip/ip/prim/rtl/prim_ram_1p_pkg.sv \
  ../vendor/lowrisc_ip/ip/prim/rtl/prim_secded_pkg.sv \
  ../rtl/ibex_alu.sv \
  ../rtl/ibex_branch_predict.sv \
  ../rtl/ibex_compressed_decoder.sv \
  ../rtl/ibex_controller.sv \
  ../rtl/ibex_core.sv \
  ../rtl/ibex_counter.sv \
  ../rtl/ibex_cs_registers.sv \
  ../rtl/ibex_csr.sv \
  ../rtl/ibex_decoder.sv \
  ../rtl/ibex_dummy_instr.sv \
  ../rtl/ibex_ex_block.sv \
  ../rtl/ibex_fetch_fifo.sv \
  ../rtl/ibex_icache.sv \
  ../rtl/ibex_id_stage.sv \
  ../rtl/ibex_if_stage.sv \
  ../rtl/ibex_load_store_unit.sv \
  ../rtl/ibex_lockstep.sv \
  ../rtl/ibex_multdiv_fast.sv \
  ../rtl/ibex_multdiv_slow.sv \
  ../rtl/ibex_pmp.sv \
  ../rtl/ibex_prefetch_buffer.sv \
  ../rtl/ibex_register_file_latch.sv \
  ../rtl/ibex_top.sv \
  ../rtl/ibex_wb_stage.sv"
yosys "read_systemverilog -link"

if { $lr_synth_ibex_branch_target_alu } {
  yosys "chparam -set BranchTargetALU 1 $lr_synth_top_module"
}

if { $lr_synth_ibex_writeback_stage } {
  yosys "chparam -set WritebackStage 1 $lr_synth_top_module"
}

yosys "chparam -set RV32B $lr_synth_ibex_bitmanip $lr_synth_top_module"

yosys "chparam -set RV32M $lr_synth_ibex_multiplier $lr_synth_top_module"

yosys "chparam -set RegFile $lr_synth_ibex_regfile $lr_synth_top_module"

yosys "synth $flatten_opt -top $lr_synth_top_module"
yosys "opt -purge"

yosys "write_verilog $lr_synth_pre_map_out"

# Map latch primitives onto latch cells
yosys "techmap -map rtl/latch_map.v"

yosys "dfflibmap -liberty $lr_synth_cell_library_path"
yosys "opt"

set yosys_abc_clk_period [expr $lr_synth_clk_period - $lr_synth_abc_clk_uprate]

if { $lr_synth_timing_run } {
  yosys "abc -liberty $lr_synth_cell_library_path -constr $lr_synth_abc_sdc_file_in -D $yosys_abc_clk_period"
} else {
  yosys "abc -liberty $lr_synth_cell_library_path"
}

yosys "clean"
yosys "write_verilog $lr_synth_netlist_out"

if { $lr_synth_timing_run } {
  # Produce netlist that OpenSTA can use
  yosys "setundef -zero"
  yosys "splitnets"
  yosys "clean"
  yosys "write_verilog -noattr -noexpr -nohex -nodec $lr_synth_sta_netlist_out"
}

yosys "check"
yosys "log ======== Yosys Stat Report ========"
yosys "tee -o $lr_synth_out_dir/reports/area.rpt stat -liberty $lr_synth_cell_library_path"
yosys "log ====== End Yosys Stat Report ======"

