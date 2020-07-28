#  Ibex Pointer Authentication Test

Ibex Pointer Authentication Test is an application to test pac/aut instructions
added for pointer authentication. This test confirms that pac/aut instructions
can be executed correctly, and that an exception occurs in case a pointer is
used without authentication. We are using Ibex Simple System, so see
`examples/simple_system/README.md` for the more details.

## Prerequisites

Basically, you need the prerequisites written
`examples/simple_system/README.md`. However, please use the rv32imcb Tool
Versions for the RISC-V Compiler Toolchain. The aut instruction executed in
this test uses the R4-type format (three source registers rs1, rs2, rs3 and
one destination register rd). This format is only used by floating-point
fused multiply-add (F) and some bit-manipulation (B) instructions.

Therefore, you have to use a compiler that supports the bitmanip extension.
The required toolchain can be found
[here](https://github.com/lowRISC/lowrisc-toolchains/releases).

## Building Simulation

The Simple System simulator binary can be built via FuseSoC.
From the Ibex repository root run:

```
fusesoc --cores-root=. run --target=sim --setup --build lowrisc:ibex:ibex_simple_system --RV32M=1 --RV32E=0 --PMPEnable=1 --PointerAuthentication=1
```

## Building Software

To build the pointer authentication test application, from the Ibex repository
root run:

```
make -C examples/sw/simple_system/pa_test
```

## Running the Simulator

Having built the simulator and software, from the Ibex repository root run:

```
./build/lowrisc_ibex_ibex_simple_system_0/sim-verilator/Vibex_simple_system -t --meminit=ram,./examples/sw/simple_system/pa_test/pa_test.elf
```

Outputting some simulation statistics:

```
Simulation statistics
=====================
Executed cycles:  1788
Wallclock time:   1.452 s
Simulation speed: 1231.4 cycles/s (1.2314 kHz)
Trace file size:  485595 B

You can view the simulation traces by calling
$ gtkwave sim.fst

Performance Counters
====================
Cycles:                     1784
NONE:                       0
Instructions Retired:       1259
LSU Busy:                   5
Fetch Wait:                 268
Loads:                      113
Stores:                     174
Jumps:                      51
Conditional Branches:       216
Taken Conditional Branches: 183
Compressed Instructions:    577
Multiply Wait:              0
Divide Wait:                0
PAC Instructions:           2
AUT Instructions:           1
```

The simulator produces several output files

* `ibex_simple_system.log` - The ASCII output written via the output peripheral
* `ibex_simple_system_pcount.csv` - A csv of the performance counters
* `trace_core_00000000.log` - An instruction trace of execution

Checkout ibex_simple_system.log to verify the that the exception
due to de-referencing an unauthenticated pointer is actually happening:

```
pointer0: A0001000
pointer1: 05CC012B
pointer0: 00001000
pointer1: 05CC012B
EXCEPTION!!!
============
MEPC:   0x00100510
MCAUSE: 0x00000007
MTVAL:  0xA01FFFDC
```
