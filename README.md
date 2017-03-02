# **zero-riscy**: RISC-V Core

**zero-riscy** is a small 3-stage RISC-V core derived from RI5CY.

**zero-riscy** fully implements the RV32IC instruction set and a minimal set of RISCV privileged v1.9 specifications.

In particular, **zero-riscy** supports the following machine-level CSR addresses: mhartid, mepc, mcause and the MIE/MPIE fields of the mstatus.

**zero-riscy** supports debug. The debug unit has been ported from RI5CY and it has the same specifications reported in http://www.pulp-platform.org/wp-content/uploads/2017/02/ri5cy_user_manual.pdf at page 26.

Roadmap for future features includes:

Complete support for M extension.

Support for RV32EC[M] extension.

Supports for performance counters.


