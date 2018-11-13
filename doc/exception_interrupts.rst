.. _exceptions-interrupts:

Exceptions and Interrupts
=========================

ZERO-RISCY supports interrupts, exceptions on illegal instructions.

+------------+-----------------------------+
| Address    | Description                 |
+============+=============================+
| **0x00** - | Interrupts 0 – 31           |
| **0x7C**   |                             |
+------------+-----------------------------+
| **0x80**   | Reset                       |
+------------+-----------------------------+
| **0x84**   | Illegal Instruction         |
+------------+-----------------------------+
| **0x88**   | ECALL Instruction Executed  |
+------------+-----------------------------+

The base address of the interrupt vector table is given by the boot address. The most significant  3 bytes of the boot address given to the core are used for the first instruction fetch of the core and as the basis of the interrupt vector table. The core starts fetching at the address made by concatenating the most significant 3 bytes of the boot address and the reset value (0x80) as the least significant byte. The boot address can be changed after the first instruction was fetched to change the interrupt vector table address. It is assumed that the boot address is supplied via a register to avoid long paths to the instruction fetch unit.


Interrupts
----------

Interrupts can only be enabled/disabled on a global basis and not individually. It is assumed that there is an event/interrupt controller outside of the core that performs masking and buffering of the interrupt lines. The global interrupt enable is done via the CSR register MSTATUS.

Multiple interrupts requests are assumed to be handled by event/interrupt controller. When an interrupt is taken, the core gives an acknowledge signal to the event/interrupt controller as well as the interrupt id taken.


Exceptions
----------

The illegal instruction exception and ecall instruction exceptions cannot be disabled and are always active.


Handling
--------

ZERO-RISCY does support nested interrupt/exception handling. Exceptions inside interrupt/exception handlers cause another exception, thus exceptions during the critical part of your exception handlers, i.e. before having saved the MEPC and MESTATUS registers, will cause those register to be overwritten. Interrupts during interrupt/exception handlers are disabled by default, but can be explicitly enabled if desired.

Upon executing an mret instruction, the core jumps to the program counter saved in the CSR register MEPC and restores the MPIE value of the register MSTATUS to IE. When entering an interrupt/exception handler, the core sets MEPC to the current program counter and saves the current value of MIE in MPIE of the MSTATUS register.
