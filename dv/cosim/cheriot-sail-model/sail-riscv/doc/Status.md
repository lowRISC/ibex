The Sail specification currently captures the following ISA features:

- The RV32I and RV64I primary base ISAs.

- The M (multiply/divide), A (atomic), and C (compressed) Standard
  Extensions.

- The F (single-precision) and D (double-precision) Floating-Point
  Standard Extensions.  This is only executable in the C emulator,
  which uses the SoftFloat C library.

- The Zicsr Control and Status Register Standard Extension.

- The N Standard Extension for User-Level Interrupts.

- The Base Counters and Timers.

- The Machine-Level and Supervisor-Level ISAs for RV32 and RV64.

- Physical Memory Protection (PMP)

For the RVWMO memory consistency model, this Sail ISA semantics is integrated with the RVWMO operational model in [the
RMEM tool](https://github.com/rems-project/rmem).

The Sail specification is parameterized over the following
platform-specific options:

- handling of misaligned data accesses with or without M-mode traps.

- updating of the PTE dirty bit with or without architectural
  exceptions.

- the contents of the `mtval` register on an illegal instruction
  exception.

The following ISA features are specified in the
prose RISC-V ISA specification but not currently in the Sail
specification.

- The RV32E and RV64E subsets of the primary base RV32I and RV64I
  integer ISAs.

- The RV128 primary base ISA.

- Specification and implementation of Endianness Control.

- Support for changing XLEN or base ISA control using the {M,S,U}XL
  fields of `mstatus`.  The model only supports
  `MXLEN`=`SXLEN`=`ULEN`.

- A complete definition of all hardware performance counters.
  These are used to count platform-specific events, and hence
  platform-dependent.

- A specification of the Physical Memory Attributes (PMAs) for the
  physical memory map.

- The Hypervisor Extension.
