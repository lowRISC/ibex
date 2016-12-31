# littleRISCV: RISC-V Core

littleRISCV is a smaller 4-stage RISC-V core. It is a more configurable version of the RI5CY core, which started its life as a
fork of the OR10N CPU core (OpenRISC ISA).

littleRISCV fully implements the RV32I instruction set, the multiply instruction from RV32M, RV32C and many custom instruction set extensions that improve its performance for signal processing applications.

Additional features include

* hardware loop
* post/pre increment
* vector operations (RV32V)
* bit operations (RV32B)
* shuffling
* rotate

and many more.

It can be configured to remove many non-needed compontents (e.g. multiplier), and enable more area-efficient versions of the modules (e.g. a smaller prefetch buffer, RV32E) for use as a lighter control core.

The core was developed as part of the [PULP platform](http://pulp.ethz.ch/) for
energy-efficient computing and is currently used as the processing core for
PULP and PULPino.

## Configuration

The core can be configured to ones need by disabling non-needed capabilities in `/include/riscv_config.sv`. You can find some example configurations in `/scripts/example_configs/`.

To overwrite, test, synthesize, and generate a clean version of all these configurations use the tool `scripts/ri5cly-manage.py`.

Just open it's help for more information

    python3 ./scripts/ri5cly-manage.py --help

## Documentation

A datasheet that explains the most important features of the core can be found
in `docs/datasheet/`.

It is written using LaTeX and can be generated as follows

    make all

