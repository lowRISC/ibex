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


// littleRISCV configuration. Decomment to enable.

// CONFIG: MUL_SUPPORT
// will enable RISCV32M support for multiplication, division, MAC operations. Uses a lot of multiplications
//`define MUL_SUPPORT

// CONFIG: VEC_SUPPORT
// will enable RISCV32V support for vector operations.
//`define VEC_SUPPORT

// CONFIG: HWL_SUPPORT
// will enable hardware loop support.
//`define HWL_SUPPORT

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


// Dependent definitions

// enables 3r2w reg file (rather than 2r1w)
//`define THREE_PORT_REG_FILE


`ifndef MUL_SUPPORT
`ifndef VEC_SUPPORT
`ifndef BIT_SUPPORT
`ifndef LSU_ADDER_SUPPORT
`ifndef PREPOST_SUPPORT
`ifndef MATH_SPECIAL_SUPPORT

// use simplified ALU
`define SIMPLE_ALU

`endif
`endif
`endif
`endif
`endif
`endif
