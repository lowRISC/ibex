# Ibex: RISC-V Core

Ibex is a small 32 bit RISC-V core with a 2-stage pipeline.

Ibex fully implements the RV32IMC instruction set and a small set of RISC-V
privileged specifications. Ibex can be configured to be very small by disabling
the RV32M extensions and by activating the RV32E extensions.

This core was initially developed as part of the 
[PULP platform](http://pulp.ethz.ch/) under the name "Zero-riscy", and has
been contributed to [lowRISC](https://www.lowrisc.org) who maintains it and
develops it further.

Ibex is under active development, with further code cleanups, feature
additions, and test and verification planned for the future.

## Documentation

A datasheet that explains the most important features of the core can be found
in the doc folder.

## License

Unless otherwise noted, everything in this repository is covered by the Apache
License, Version 2.0 (see LICENSE for full text).
