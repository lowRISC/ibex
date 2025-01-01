This directory contains binaries that are not easy to compile.

RTOSDemo32.axf and RTOSDemo64.axf are created by checking out
https://github.com/FreeRTOS/FreeRTOS, following the instructions in
`FreeRTOS/Demo/RISC-V-spike-htif_GCC/README.md`, and building:
* `make XLEN=32 BASE_ADDRESS=0x10100000`
* `make XLEN=64 BASE_ADDRESS=0x1212340000`
