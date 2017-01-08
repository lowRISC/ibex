// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                 Markus Wegmann - markus.wegmann@technokrat.ch              //
//                                                                            //
// Design Name:    RISC-V config file                                         //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Configure optional simulation modules                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// no traces for synthesis, they are not synthesizable
`ifndef SYNTHESIS
`ifndef PULP_FPGA_EMUL
`define TRACE_EXECUTION
`endif
//`define SIMCHECKER
`endif


// littleRISCV configuration. 

// Decomment to enable.

// The format should be strictly followed so the ri5cly-manage tool can parse the configuration
// A CONFIG section declares a config definition, a CONFIG_REGION enables the tool to remove disabled code
// for export. See the ri5cly-manage.py tool help and source code in the /scripts folder for more information.



// CONFIG: MUL_SUPPORT
// will enable RISCV32M support for multiplication, division, MAC operations. Uses a lot of multiplications
//`define MUL_SUPPORT

// CONFIG: VEC_SUPPORT
// will enable RISCV32V support for vector operations.
//`define VEC_SUPPORT

// CONFIG: HWLP_SUPPORT
// will enable hardware loop support.
//`define HWLP_SUPPORT

// CONFIG: BIT_SUPPORT
// will enable bit manipulation and counting support.
//`define BIT_SUPPORT

// CONFIG: LSU_ADDER_SUPPORT
// will enable an additional adder in the LSU for better timings.
//`define LSU_ADDER_SUPPORT

`ifdef LSU_ADDER_SUPPORT

// CONFIG: PREPOST_SUPPORT
// will enable pre/post increment load/store support support.
//`define PREPOST_SUPPORT

`endif // LSU_ADDER_SUPPORT

// CONFIG: MATH_SPECIAL_SUPPORT
// will enable clip, min and max operations support.
//`define MATH_SPECIAL_SUPPORT


// CONFIG: JUMP_IN_ID
// will enable direct jump in ID. Might increase critical path of jump target.
`define JUMP_IN_ID


// Dependent definitions

// CONFIG: THREE_PORT_REG_FILE
// enables 3r2w reg file (rather than 2r1w)
//`define THREE_PORT_REG_FILE


`ifndef MUL_SUPPORT
`ifndef VEC_SUPPORT
`ifndef BIT_SUPPORT
`ifndef LSU_ADDER_SUPPORT
`ifndef PREPOST_SUPPORT
`ifndef MATH_SPECIAL_SUPPORT

// CONFIG: SIMPLE_ALU
// will enable simplified ALU for less gates. It does not support vectors, shuffling, nor bit operations.
`define SIMPLE_ALU

// CONFIG: SMALL_IF
// will disable large FIFO in IF stage and use a more simple one.
`define SMALL_IF

// CONFIG: RV32E
// will reduce the register file to 16 words
`define RV32E

// CONFIG: ONLY_ALIGNED
// will only allow aligned memory accesses and therefore overlapping mustn't occur
//`define ONLY_ALIGNED

// CONFIG: SPLITTED_ADDER
// will split ALU Adder in half and use two cycles to add operands
//`define SPLITTED_ADDER

`ifdef SMALL_IF
`ifndef JUMP_IN_ID
// CONFIG: NO_JUMP_ADDER
// (NOT IMPLEMENTED!!!) will use ALU adder to calculate target and return address from prefetcher
//`define NO_JUMP_ADDER
`endif
`endif


`ifndef SPLITTED_ADDER
`ifndef NO_JUMP_ADDER
`ifdef 	JUMP_IN_ID
// CONFIG: MERGE_ID_EX
// will merge/fuse the ID and EX stage
//`define MERGE_ID_EX
`endif
`endif
`endif

`endif
`endif
`endif
`endif
`endif
`endif
