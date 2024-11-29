# ISOLDE Loosely-coupled accelerator (LCA) model. 
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
in folder **isolde/lca_system**:  
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
make TEST=fibonacci veri-clean clean-test  verilate  test-app veri-run
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
Default test is **vlinstr_test**.  
# REDMULE testing
## build test app
* **gcc** toolchain
```
make golden
make sim-inputs
```
* **llvm** toolchain
*Not implemented*
## execute test
```
make TEST=redmule clean-test sim-inputs veri-clean verilate veri-run
```
Output should be similar to this
```
[TESTBENCH] @ t=0: loading firmware /home/uic52463/hdd1/tristan-project/ibex/isolde/lca_system/sw/bin/redmule-m.hex
TOP.tb_lca_system.u_top.u_ibex_tracer.unnamedblk2.unnamedblk3: Writing execution trace to trace_core_00000000.log
Timing for REDMULE_LCA: 240 cycles
Resumed!
[TB LCA] @ t=10374 - Success!
[TB LCA] @ t=10374 - errors=00000000
```  


---  
---