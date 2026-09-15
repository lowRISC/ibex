Notes on F and D extensions (floating point) in the SAIL RISC-V Model
=====================================================================

Questions? Rishiyur Nikhil (github id: `rsnikhil`), Bluespec, Inc.

The main original SAIL RISC-V repo is [here](https://github.com/rems-project/sail-riscv)

[Current working directory](https://github.com/rsnikhil/sail-riscv.git).
This is a fork of the main original repo, on which we have added the SAIL code for F and D extensions.
This will be merged back into the main original repo after testing.

---

Status (2019-10-24)
-------------------

1. Complete (almost): SAIL coding [Rishiyur Nikhil, Bluespec, Inc.]
   Remaining: tweaks to handle illegal rounding modes.
2. In progress: Incorporate Berkeley SoftFloat calls [U.Cambridge]
3. To do: Testing on all ISA tests

Should not take more than a few days to complete the remaining work.

---

Files (all are in "model/" directory)
-------------------------------------

Changed file:
Added two one-line predicates `haveFExt()` and `haveDExt()` that test whether MISA.F and MISA.D are set:

        riscv_sys_regs.sail

New files:
Definition for FLEN and bit-vectors holding floating point values.
The former should be used if only F is supported,
the latter if F and D are supported:

        riscv_flen_F.sail
        riscv_flen_D.sail

New file: A few more definitions for floating point registers.

        riscv_freg_type.sail

New file: The floating point register file and floating point CSRs:

        riscv_fdext_regs.sail

New files: The main files for F and D, respectively, containing AST
definitions, binary encode/decode mappings, assembly code generation,
and execution semantics:

        riscv_insts_fext.sail
        riscv_insts_dext.sail

Functions that call out to Berkeley SoftFloat (implemented in C) to
perform the core floating point computations:

        riscv_softfloat_interface.sail
