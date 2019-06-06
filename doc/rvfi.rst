.. _rvfi:

RISC-V Formal Interface
=======================

Ibex is adapted to support the interface defined by RISC-V Formal Interface
(`riscv-formal <https://github.com/SymbioticEDA/riscv-formal/blob/master/docs/rvfi.md>`_).
The signals provide an insight to the state of the core.
Generally speaking the interface decodes the current instruction.
This includes the opcode, the source and destination registers,
the program counter and for memory operations the memory location and data.


Formal Verification
-------------------

The signals provided by RVFI can be used to formally verify the adherents of
Ibex to the RISC-V `specification <https://riscv.org/specifications/>`_.
Currently the implementation is restricted to support the `I` and `C` extensions.

At the moment Ibex is not formally verified, a previous version (zero-riscy)
was tested, but this required changes to the core as well as to the tool used
in the process (`yosys <https://github.com/YosysHQ/yosys>`_). Support is work in progress.
