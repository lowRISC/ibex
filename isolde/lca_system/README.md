# ISOLDE Loosely-coupled accelerator (LCA) model. 
## [REDMULE](https://github.com/ISOLDE-Project/redmule) hardware accelerator
Details about the accelerator are [here](https://github.com/ISOLDE-Project/redmule?tab=readme-ov-file#redmule)
## Prerequisites
in root folder execute
```
. ./eth.sh
```
## Building Simulation
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
```sh
make veri-clean verilate
``` 

## build test app
* **gcc** toolchain
```
make golden
make sim-inputs
```
* **llvm** toolchain
*Not implemented*
## execute test
```sh
make TEST=redmule test-clean sim-inputs veri-run
```
Output should be similar to this
```
[TESTBENCH] @ t=0: loading firmware /ubuntu_20.04/home/ext/tristan-project/ibex/isolde/lca_system/sw/bin/redmule-m.hex
TOP.tb_lca_system.u_top.u_ibex_tracer.unnamedblk2.unnamedblk3: Writing execution trace to trace_core_00000000.log
Timing for REDMULE: 240 cycles
Resumed!
Terminated test with 0 errors. See you!
```  
# REDMULE testing
```sh
make sim-inputs
make TEST=redmule  veri-run
```
# Regression
```sh
make TEST=fibonacci test-clean test-build veri-run
```
---  
---
