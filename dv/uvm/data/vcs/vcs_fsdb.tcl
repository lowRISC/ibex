# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# TCL file invoked from VCS's simv at run-time using this: -ucli -do <this file>

if {[info exists ::env(WAVES)]} {
# Use FSDB for dumping only if Verdi is set up

# Syntax: fsdbDumpvars [depth] [instance] [option]*
##############################################################################
# Option                     Description
##############################################################################
# +mda                       Dumps memory and MDA signals in all scopes.
# +packedmda                 Dumps packed signals
# +struct                    Dumps structs
# +skip_cell_instance=mode  Enables or disables cell dumping
# +strength                  Enables strength dumping
# +parameter                 Dumps parameters
# +power                     Dumps power-related signals
# +trace_process             Dumps VHDL processes
# +no_functions              Disables dumping of functions
# +sva                       Dumps assertions
# +Reg_Only                  Dumps only reg type signals
# +IO_Only                   Dumps only IO port signals
# +by_file=<filename>        File to specify objects to add
# +all                       Dumps memories, MDA signals, structs, unions,power, and packed structs

  if {$::env(WAVES) == 1} {
    if { [info exists ::env(VERDI_HOME)] } {
      fsdbDumpfile  $::env(DUMP_FILE)
      fsdbDumpvars  0 $::env(TB_TOP) +all
      fsdbDumpSVA   0 $::env(TB_TOP)
    } else {
      # Verdi is not set up, so use standard dumping format
      set dump_file $::env(DUMP_FILE)
      dump -file "${dump_file}"
      dump -add { tb } -depth 0 -aggregates -scope "."
    }
  }
}

run
quit
