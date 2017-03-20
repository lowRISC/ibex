# **zero-riscy**: RISC-V Core

**zero-riscy** is a small 3-stage RISC-V core derived from RI5CY.

**zero-riscy** fully implements the RV32IMC instruction set and a minimal set of RISCV privileged v1.9 specifications.

In particular, **zero-riscy** supports the following machine-level CSR addresses: mhartid, mepc, mcause and the MIE/MPIE fields of the mstatus.

**zero-riscy** supports debug. The debug unit has been ported from RI5CY and it has the same specifications reported in http://www.pulp-platform.org/wp-content/uploads/2017/02/ri5cy_user_manual.pdf at page 26.

**zero-riscy** can be configured to be very small by disabling the RV32M extensions and by activating the RV32E extensios.

Roadmap for future features includes:

Supports for performance counters.


