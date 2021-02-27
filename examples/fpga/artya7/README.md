# Ibex RISC-V Core SoC Example

Please see [examples](https://ibex-core.readthedocs.io/en/latest/02_user/examples.html "Ibex User Manual") for a description of this example.

## Requirements

### Tools

  - RV32 compiler
  - srecord
  - `fusesoc` and its dependencies
  - Xilinx Vivado

### Hardware

  - Either a Digilent Arty A7-35 oder A7-100 board

## Build

The easiest way to build and execute this example is to call the following make goals from the root directory.

Use the following for the Arty A7-35

```
make build-arty-35 program-arty
```

and for the Arty A7-100

```
make build-arty-100 program-arty
```

### Software

First the software must be built. Go into `examples/sw/led` and call:

```
make CC=/path/to/RISC-V-compiler
```

The setting of `CC` is only required if `riscv32-unknown-elf-gcc` is not available through the `PATH` environment variable.
The path to the RV32 compiler `/path/to/RISC-V-compiler` depends on the environment.
For example, it can be for example `/opt/riscv/bin/riscv-none-embed-gcc` if the whole path is required or simply the name of the executable if it is available through the `PATH` environment variable.

This should produce a `led.vmem` file which is used in the synthesis to update the SRAM storage.

### Hardware

Run either of the following commands at the top level to build the respective hardware.
Both variants of the Arty A7 are supported and can be selected via the `--parts` parameter.

```
fusesoc --cores-root=. run --target=synth --setup --build lowrisc:ibex:top_artya7 --part xc7a35ticsg324-1L
```

```
fusesoc --cores-root=. run --target=synth --setup --build lowrisc:ibex:top_artya7 --part xc7a100tcsg324-1
```

This will create a directory `build` which contains the output files, including
the bitstream.

## Program

After the board is connected to the computer it can be programmed with:

```
fusesoc --cores-root=. run --target=synth --run lowrisc:ibex:top_artya7
```

LED1/LED3 and LED0/LED2 should alternately be on after the FPGA programming is finished.

## Debug

By default, a debug unit compliant with the [RISC-V debug specification](https://github.com/riscv/riscv-debug-spec) v0.13.1 is integrated and is available via JTAG pins on PMOD header JD; the pinouts are:

| PMOD header JD |            |
| ------------ | ------------ |
| 1  : TDO     | 7  : TDI     |
| 2  : TRST_N  | 8  : TMS     |
| 3  : TCK     | 9  : RESET_N |
| 4            | 10 :         |
| 5  : GND     | 11 : GND     |
| 6  : VREF    | 12 : VREF    |

The Arty board JTAG pinout is a defacto standard by SiFive promulgated in their documents [SiFive Freedom E310 Arty FPGA Dev Kit Getting Started Guide](https://www.sifive.com/documentation/freedom-soc/freedom-e300-arty-fpga-dev-kit-getting-started-guide/) (see Section 2.2), [SiFive Core IP FPGA Eval Kit User Guide Version v2019p05](https://sifive.cdn.prismic.io/sifive%2Fa76dc011-5d11-4d73-9e7a-900640d76f3d_fpga-getting-started_v2019p05.pdf) (see Section 3.2), and [SiFive Core IP FPGA Eval Kit User Guide Version v19.08p0](https://sifive.cdn.prismic.io/sifive%2Ff290f543-87e9-4e0b-8a4a-6287217f79bc_coreip-fpga-eval-userguide-v19_08.pdf) (see Section 3.2).

