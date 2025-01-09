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
 make TEST=vlinstr_test test-clean test-build veri-run
```

## build test app
* **gcc** toolchain
```
make golden
make sim-input
```
* **llvm** toolchain
*Not implemented*
 
# REDMULE testing
## 128b custom instruction

```sh
make  veri-clean verilate test-clean sim-input TEST_CFLAGS=-DCUSTOM_128B veri-run
make  test-clean sim-input TEST_CFLAGS=-DCUSTOM_128B veri-run
```
Expected output:
```
[TESTBENCH] @ t=0: loading /home/uic52463/hdd1/tristan-project/ibex/isolde/tca_system/sw/bin/redmule_complex-m.hex into imemory
[TESTBENCH] @ t=0: loading /home/uic52463/hdd1/tristan-project/ibex/isolde/tca_system/sw/bin/redmule_complex-d.hex into dmemory
TOP.tb_tca_system.u_top.u_ibex_tracer.unnamedblk2.unnamedblk3: Writing execution trace to trace_core_00000000.log
[APP TCA custom-128b] Starting test. Godspeed!
Timing for REDMULE_TCA_VLI: 226 cycles
[APP TCA custom-128b] Terminated test with 0 errors. See you!
[TB TCA] @ t=14306 - Success!
[TB TCA] @ t=14306 - errors=00000000
[TB TCA] @ t=14306 - writes[imemory] =          0
[TB TCA] @ t=14306 - reads [imemory] =       6262
[TB TCA] @ t=14306 - writes[dmemory] =        464
[TB TCA] @ t=14306 - reads [dmemory] =        716
[TB TCA] @ t=14306 - writes[stack] =        106
[TB TCA] @ t=14306 - reads [stack] =        101
```
## 32b custom instruction
```sh
make  test-clean sim-input TEST_CFLAGS=-DCUSTOM_32B veri-run
```
Expected output:
```
[TESTBENCH] @ t=0: loading /home/uic52463/hdd1/tristan-project/ibex/isolde/tca_system/sw/bin/redmule_complex-m.hex into imemory
[TESTBENCH] @ t=0: loading /home/uic52463/hdd1/tristan-project/ibex/isolde/tca_system/sw/bin/redmule_complex-d.hex into dmemory
TOP.tb_tca_system.u_top.u_ibex_tracer.unnamedblk2.unnamedblk3: Writing execution trace to trace_core_00000000.log
[APP TCA custom-32b] Starting test. Godspeed!
Timing for REDMULE_TCA: 230 cycles
[APP TCA custom-32b] Terminated test with 0 errors. See you!
[TB TCA] @ t=14138 - Success!
[TB TCA] @ t=14138 - errors=00000000
[TB TCA] @ t=14138 - writes[imemory] =          0
[TB TCA] @ t=14138 - reads [imemory] =       6176
[TB TCA] @ t=14138 - writes[dmemory] =        464
[TB TCA] @ t=14138 - reads [dmemory] =        710
[TB TCA] @ t=14138 - writes[stack] =        106
[TB TCA] @ t=14138 - reads [stack] =        101
```
---
# Simulating instruction memory latency
Instruction memory latency is expressed in (core) cycles.  
## build simulations
```sh
make IMEM_LATENCY=0 verilate
make IMEM_LATENCY=17 verilate
```
## execute tests
```sh
make IMEM_LATENCY=0 test-clean  sim-input TEST_CFLAGS=-DCUSTOM_128B veri-run
make IMEM_LATENCY=17 test-clean  sim-input TEST_CFLAGS=-DCUSTOM_128B veri-run
```
---
---
---