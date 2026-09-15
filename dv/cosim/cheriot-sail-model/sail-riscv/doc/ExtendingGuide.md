Extending the model
===================

Changing the register representation
------------------------------------

One can change the base register representation from an `XLEN`-length
bitvector by supplying a different definition of the `regtype` type,
and functions that convert between that type and the default
`XLEN`-length bitvector.  The interface for this is specified in
`riscv_reg_type.sail`.  An extension can implement a different
representation in a file that follows that interface, and use it with
the rest of the model.

Adding architectural state
--------------------------

Adding registers (such as for floating-point) would involve naming
them and defining their read and write accessors, as is done for the
integer registers in `riscv_types.sail`, `riscv_reg_type.sail` and
`riscv_regs.sail`.  For modularity, these new definitions should be
added in separate files.  If any of these registers are
control-and-status registers (CSRs), or depend on
privilege level (such as hypervisor-mode registers), additional access
control checks would need to be provided as is done for the standard
CSRs in `riscv_sys_regs.sail` and `riscv_sys_control.sail`.  Access to
newly added CSRs can be hooked in `riscv_csr_ext.sail`. In addition,
the bits `mstatus.XS` and `mstatus.SD` may need to be updated
or extended to handle any extended register state.

Adding a new privilege level or functionality restricted by privilege
level will normally be accompanied by defining new exception causes
and their encodings.  This will require modifying and extending the
existing definitions for privilege levels and exceptions in
`riscv_types.sail`, and modifying the exception handling and privilege
transition functions in `riscv_sys_control.sail`.

Modifying exception handling
----------------------------

An extension that needs to interact closely with exception handling
may need to capture additional information at the time of an
exception.  This is supported using the `ext` field in the
`sync_exception` type in `riscv_sync_exception.sail`, which is where
the extension can store this information.  The addresses involved in
exception handling can be modified by following the interface provided
in `riscv_sys_exceptions.sail`.  New exception codes can be introduced
using the `E_Extension` variant of the `ExceptionType` in
`riscv_types`.

Adding low-level platform functionality
---------------------------------------

Adding support for new devices such as interrupt controllers and
similar memory-mapped I/O (MMIO) entities strictly falls outside the
purview of the formal model itself, and typically is not done
directly in the Sail model.  However, bindings to this external
functionality can be provided to Sail definitions using the `extern`
construct of the Sail language. `riscv_platform.sail` can be examined
to see how this is done for the SiFive core-local interrupt (CLINT)
controller, the HTIF timer and terminal devices.  The
implementation of the actual functionality provided by these MMIO
devices would need to be added to the C and OCaml emulators.

If this functionality requires the definition of new interrupt
sources, their encodings would need to be added to `riscv_types.sail`,
and their delegation and handling added to `riscv_sys_control.sail`.

Modifying physical memory access
--------------------------------

Physical memory addressing and access is defined in `riscv_mem.sail`.
Any new regions of memory that are accessible via physical addresses
will require modifying the `mem_read`, `mem_write_value` or their
supporting functions `checked_mem_read` and `checked_mem_write`.

The model supports storing and retrieving metadata along with memory
values at each physical memory address.  The default interface for
this is defined in `prelude_mem_metadata.sail`.  An extension can
customize the default implementation there to support its metadata
type.

The actual content of such memory, and its modification, can be
defined in separate Sail files.  This functionality will have access
to any newly defined architectural state.  One can examine how normal
physical memory access is implemented in `riscv_mem.sail` with helpers
in `prelude_mem.sail` and `prelude_mem_metadata.sail`.

Extending virtual memory and address translation
------------------------------------------------

Virtual memory is implemented in `riscv_vmem.sail`, and defining new
address translation schemes will require modifying the top-level
`translateAddr` function.  New types of memory access can be defined
using the definitions in `riscv_vmem_types`.  Any access control
checks on virtual addresses and the specifics of the new address
translation can be specified in a separate file.  This functionality
can access any newly defined architectural state.

The RV64 architecture has reserved bits in the PTE that can be
utilized for research experimentation.  These bits can be accessed and
modified using the `ext_pte` argument in functions implementing the
page-table walk.  The information computed by and used during the
page-table can also be varied using the `ext_ptw` argument, which can
be defined and used by extensions as needed.  Extensions can override
the definitions of `checkPTEPermission` and `ext_get_ptw_error` to
generate and process this custom information, and
`ext_translate_exception` to convert any custom errors into
extension-specific exceptions.

Checking and transforming memory addresses
------------------------------------------

An extension may wish to perform validity checks and transformations
on addresses generated by an instruction before a memory access is
performed with the generated address.  This is supported using the
types defined in `riscv_addr_checks_common.sail`, with a default
implementation in `riscv_addr_checks.sail`.

The handling of the memory addresses involved during exception
handling can be extending using the interface defined in
`riscv_sys_exceptions.sail`.

Checking and transforming the program counter
---------------------------------------------

An extension might want to similarly check and transform accesses to
the program counter.  This is supported by supplying implementations
of the functions defined in `riscv_pc_access.sail`.

In addition, dynamically enabling and disabling the RVC extension has
an effect on legal PC alignment; in particular, attempts to disable
RVC are ignored if the PC becomes unaligned in the base architecture.
Extensions can also veto these attempts by appropriately defining
`ext_veto_disable_C`.

Adding new instructions
-----------------------

This is typically simpler than adding new architectural state or
memory interposition.  Each new set of instructions can be specified
in a separate self-contained file, with their instruction encodings,
assembly language specifications and the corresponding encoders and
decoders, and execution semantics. `riscv.sail` can be examined for
examples on how this can done.  These instruction definitions can
access any newly defined architectural state and perform virtual or
physical memory accesses as is done in `riscv.sail`.

Interposing on instruction decode
---------------------------------

An extension may wish to check and transform a decoded instruction.
This is supported via a post-decode extension hook, the default
implementation of which is provided in `riscv_decode_ext.sail`.

General guidelines
------------------

For any new extension, it is helpful to factor it out into the above
items.  When specifying and implementing the extension, it is expected
to be easier to implement it in the above listed order.

Example
-------

As an example, one can examine the implementation of the 'N' extension
for user-level interrupt handling.  The architectural state to support
'N' is specified in `riscv_next_regs.sail`, added CSR and control
functionality is in `riscv_next_control.sail`, and added instructions
are in `riscv_insts_next.sail`.  Access to the CSRs added by the
extension are hooked in `riscv_csr_ext.sail`.

In addition, privilege transition and interrupt delegation logic in
`riscv_sys_control.sail` has been extended.
