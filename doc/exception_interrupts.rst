.. _exceptions-interrupts:

Exceptions and Interrupts
=========================

Ibex implements trap handling for interrupts and exceptions according to the RISC-V Privileged Specification, version 1.11.

All exceptions cause the core to jump to the base address of the vector table in the ``mtvec`` CSR.
Interrupts are handled in vectored mode, i.e., the core jumps to the base address plus four times the interrupt cause number.

The base address of the vector table is given by the boot address (must be aligned to 256 bytes, i.e., its least significant byte must be 0x00).
The most significant 3 bytes of the boot address given to the core are used for the first instruction fetch of the core and as the basis of the interrupt vector table.
The core starts fetching at the address made by concatenating the most significant 3 bytes of the boot address and the reset value (0x80) as the least significant byte.
The boot address can be changed after the first instruction was fetched to change the interrupt vector table address.
It is assumed that the boot address is supplied via a register to avoid long paths to the instruction fetch unit.


Interrupts
----------

Interrupts can only be enabled/disabled on a global basis and not individually.
The global interrupt enable is done via the ``mstatus`` CSR.

It is assumed that there is a separate event/interrupt controller outside of the core that performs masking and buffering of multiple interrupt requests.
When an interrupt is taken, the core gives an acknowledge signal to the external event/interrupt controller as well as the interrupt ID taken.
Check :ref:`interrupts` for more details.


Exceptions
----------

Ibex can trigger an exception due to the following exception causes:

+----------------+---------------------------------------------------------------+
| Exception Code | Description                                                   |
+----------------+---------------------------------------------------------------+
|              2 | Illegal instruction                                           |
+----------------+---------------------------------------------------------------+
|              3 | Breakpoint                                                    |
+----------------+---------------------------------------------------------------+
|              5 | Load access fault                                             |
+----------------+---------------------------------------------------------------+
|              7 | Store access fault                                            |
+----------------+---------------------------------------------------------------+
|             11 | Environment call from M-mode (ECALL)                          |
+----------------+---------------------------------------------------------------+

The illegal instruction exception, LSU error exceptions and ECALL instruction exceptions cannot be disabled and are always active.


Handling
--------

Ibex does support nested interrupt/exception handling.
Exceptions inside interrupt/exception handlers cause another exception.
However, exceptions during the critical part of your exception handlers, i.e. before having saved the ``mepc`` and ``mstatus``, will cause those CSRs to be overwritten.
Interrupts during interrupt/exception handlers are thus disabled by default, but can be explicitly enabled if desired.

When entering an interrupt/exception handler, the core sets ``mepc`` to the current program counter and saves ``mstatus``.MIE to ``mstatus``.MPIE.
Upon executing an MRET instruction, the core jumps to the program counter saved in the ``mepc`` CSR and restores ``mstatus``.MPIE to ``mstatus``.MIE.
