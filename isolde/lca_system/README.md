# ISOLDE Loosely-coupled accelerator (LCA) model. 
## [REDMULE](https://github.com/ISOLDE-Project/redmule) hardware accelerator
Details about the accelerator are [here](https://github.com/ISOLDE-Project/redmule?tab=readme-ov-file#redmule)
## Prerequisites
in folder **isolde/lca_system**:  
```
. ./eth.sh
```
## Building Simulation
in folder **isolde/lca_system**:  
* get a clean slate:
```
make redmule-update veri-clean verilate
```
or
```
make IMEM_LATENCY=1  redmule-update veri-clean verilate
```

## build the simulation and run the a test application
```sh
make veri-clean verilate
``` 

### **gcc** toolchain
```sh
make golden
make  COMPILER=gcc PE=redmule TEST=redmule test-clean test-build veri-run
```
Output should be similar to this
```
PRINT @                 764 id=         1,cycles =       229

[TB LCA] @ t=764 - reads [imemory] =         28
[TB LCA] @ t=764 - writes[dmemory] =        459
[TB LCA] @ t=764 - reads [dmemory] =        360
[TB LCA] @ t=764 - writes[stack] =          0
[TB LCA] @ t=764 - reads [stack] =          0
[APP LCA ] Terminated test  1 in 229 cycles
[LCA] Terminated test with 0 errors. See you!
```
### **llvm** toolchain
```sh
make golden
make PE=redmule TEST=redmule test-clean test-build veri-run
```
Output should be similar to this
```
PRINT @                 754 id=         1,cycles =       223

[TB LCA] @ t=754 - reads [imemory] =         22
[TB LCA] @ t=754 - writes[dmemory] =        459
[TB LCA] @ t=754 - reads [dmemory] =        360
[TB LCA] @ t=754 - writes[stack] =          0
[TB LCA] @ t=754 - reads [stack] =          0
[APP LCA ] Terminated test  1 in 223 cycles
[LCA] Terminated test with 0 errors. See you!
```    
---
# other tests
## llvm

```sh
make   TEST=dhrystone test-clean test-build veri-run
```
Output should be similar to this:
```
Cycles for one run through Dhrystone:         442
                                              44231 cycles / 100 runs
Dhrystones per 1000 cycle:                     2
[TB LCA] @ t=210212 - Success!
[TB LCA] @ t=210212 - errors=00000000
- /ubuntu_20.04/home/ext/tristan-project/ibex.tca/isolde/lca_system/tb/tb_lca_system.sv:513: Verilog $finish
```
## gcc
```sh
make   COMPILER=gcc TEST=dhrystone test-clean test-build veri-run
```
Output should be similar to this:
```
Cycles for one run through Dhrystone:         729
                                              72920 cycles / 100 runs
Dhrystones per 1000 cycle:                     1
[TB LCA] @ t=272960 - Success!
[TB LCA] @ t=272960 - errors=00000000
- /ubuntu_20.04/home/ext/tristan-project/ibex.tca/isolde/lca_system/tb/tb_lca_system.sv:513: Verilog $finish
```


# Debug Module

Assuming working directory *isolde/lca_system* and each command from bellow in a separate terminal window.  
1. start simulation
```sh
. ./eth.sh
make  DBG_MODULE=1 TEST=hello_test NO_TEE=1 test-clean test-build  veri-clean verilate veri-run
```
**Note**: Application( in this example *hello_test*) has to be an endless loop.   

2. start openocd
```sh
. ./eth.sh
openocd -f isolde.cfg 
```
3. start telnet connection
```sh
telnet localhost 4444
```
In the telnet terminal type:   
```
reset halt
reg pc 0x100000
resume
shutdown
```
or 
In the telnet terminal type( make sure that your working directory is **isolde/lca_system)**:   
```
source ./read_test.tcl
```
or
```
source imem_test.tcl
```
### kill telnet connection
```sh
lsof -i :6666
```
Output:
```
COMMAND   PID USER   FD   TYPE    DEVICE SIZE/OFF NODE NAME
openocd 27459  dan    5u  IPv4 558111571      0t0  TCP localhost:6666 (LISTEN)
```
```sh
kill -9 27459
```
# OpenOCD General Commands
[https://openocd.org/doc/html/General-Commands.html?utm_source=chatgpt.com](https://openocd.org/doc/html/General-Commands.html?utm_source=chatgpt.com)
# Known issues
 RISC-V memory access method(s) shall be used as follow:
 - *progbuf*  for reading/writting dmem and stack
 - *sysbus*   for reading/writting imem