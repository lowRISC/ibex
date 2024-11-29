# ISOLDE Tightly-coupled accelerator (TCA) model.
## [REDMULE](https://github.com/ISOLDE-Project/redmule) hardware accelerator
Details about the accelerator are [here](https://github.com/ISOLDE-Project/redmule?tab=readme-ov-file#redmule)
## Prerequisites
in root folder execute
```
. ./eth.sh
```
## Building Simulation
default value for **IBEX_CONFIG**=*isolde*.  
For a list of possible configurations, see [ibex_configs.yaml](../../ibex_configs.yaml)  
in folder **isolde/simple_system**:  
* get a clean slate:
```
make veri-clean clean-test
```
or
```
make veri-clean clean-test-programs
```

## build the simulation and run the a test application
```
make TEST=fibonacci veri-clean verilate clean-test test-app run-test2
``` 
Output should be similar to this:  
```
TOP.tb_lca_system.u_top.u_ibex_tracer.unnamedblk2.unnamedblk3: Writing execution trace to trace_core_00000000.log
starting fib(15)...
fib(0) = 0
fib(1) = 1
fib(2) = 1
fib(3) = 2
fib(4) = 3
fib(5) = 5
fib(6) = 8
fib(7) = 13
fib(8) = 21
fib(9) = 34
fib(10) = 55
fib(11) = 89
```
you can replace *fibonacci* with any test from isolde/sw/simple_system, e.g. make TEST=**dhrystone** veri-clean clean-test  verilate  test-app veri-run.  
Default test is **redmule_complex**.
**Examples**  
```sh
make TEST=vlinstr_test clean-test test-app run-test2

make TEST=vlinstr_test veri-clean verilate clean-test test-app run-test2
```

## build test app
* **gcc** toolchain
```
make golden
make sim-inputs
```
* **llvm** toolchain
*Not implemented*
 
# REDMULE testing
```sh
 make veri-clean verilate clean-test sim-input run-test2
```
Expected output:
```
[TESTBENCH] @ t=0: loading /ubuntu_20.04/home/ext/tristan-project/ibex/isolde/tca_system/sw/bin/redmule_complex-m.hex into imemory
[TESTBENCH] @ t=0: loading /ubuntu_20.04/home/ext/tristan-project/ibex/isolde/tca_system/sw/bin/redmule_complex-d.hex into dmemory
TOP.tb_tca_system.u_top.u_ibex_tracer.unnamedblk2.unnamedblk3: Writing execution trace to trace_core_00000000.log
[APP TCA] Starting test. Godspeed!
Timing for REDMULE_TCA: 231 cycles
[APP TCA] Terminated test with 0 errors. See you!
[TB TCA] @ t=13506 - Success!
[TB TCA] @ t=13506 - errors=00000000
- /ubuntu_20.04/home/ext/tristan-project/ibex/isolde/tca_system/tb/tb_tca_system.sv:462: Verilog $finish
mv verilator_tb.vcd /ubuntu_20.04/home/ext/tristan-project/ibex/isolde/tca_system/log/tb_tca_system/redmule_complex.vcd
```

---  
---