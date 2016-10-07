# RI5CY: RISC-V Core

RI5CY is a small 4-stage RISC-V core. It started its life as a
fork of the OR10N CPU core that is based on the OpenRISC ISA.

RI5CY fully implements the RV32I instruction set, the multiply instruction from
RV32M and many custom instruction set extensions that improve its performance
for signal processing applications.

The core was developed as part of the [PULP platform](http://pulp.ethz.ch/) for
energy-efficient computing and is currently used as the processing core for
PULP and PULPino.

## Documentation

A datasheet that explains the most important features of the core can be found
in `docs/datasheet/`.

It is written using LaTeX and can be generated as follows

    make all
