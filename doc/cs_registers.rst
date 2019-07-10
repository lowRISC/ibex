.. _cs-registers:

Control and Status Registers
============================

Ibex implements all the Control and Status Registers (CSRs) listed in the following table according to the RISC-V Privileged Specification, version 1.11.

+---------+--------------------+--------+-----------------------------------------------+
| Address |   Name             | Access | Description                                   |
+=========+====================+========+===============================================+
|  0x300  | ``mstatus``        | WARL   | Machine Status                                |
+---------+--------------------+--------+-----------------------------------------------+
|  0x301  | ``misa``           | WARL   | Machine ISA and Extensions                    |
+---------+--------------------+--------+-----------------------------------------------+
|  0x305  | ``mtvec``          | R      | Machine Trap-Vector Base Address              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x320  | ``mcountinhibit``  | RW     | Machine Counter-Inhibit Register              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x323  | ``mhpmevent3``     | WARL   | Machine Performance-Monitoring Event Selector |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x33F  | ``mhpmevent31``    | WARL   | Machine performance-monitoring event selector |
+---------+--------------------+--------+-----------------------------------------------+
|  0x340  | ``mscratch``       | RW     | Machine Scratch Register                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x341  | ``mepc``           | WARL   | Machine Exception Program Counter             |
+---------+--------------------+--------+-----------------------------------------------+
|  0x342  | ``mcause``         | WLRL   | Machine Cause Register                        |
+---------+--------------------+--------+-----------------------------------------------+
|  0x343  | ``mtval``          | WARL   | Machine Trap Value Register                   |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B0  | ``dcsr``           | RW     | Debug Control and Status Register             |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B1  | ``dpc``            | RW     | Debug PC                                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B2  | ``dscratch0``      | RW     | Debug Scratch Register 0                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0x7B3  | ``dscratch1``      | RW     | Debug Scratch Register 1                      |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB00  | ``mcycle``         | RW     | Machine Cycle Counter                         |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB02  | ``minstret``       | RW     | Machine Instructions-Retired Counter          |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB03  | ``mhpmcounter3``   | WARL   | Machine Performance-Monitoring Counter        |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB1F  | ``mhpmcounter31``  | WARL   | Machine Performance-Monitoring Counter        |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB80  | ``mcycleh``        | RW     | Upper 32 bits of ``mcycle``                   |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB82  | ``minstreth``      | RW     | Upper 32 bits of ``minstret``                 |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB83  | ``mhpmcounter3h``  | WARL   | Upper 32 bits of ``mhmpcounter3``             |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0xB9F  | ``mhpmcounter31h`` | WARL   | Upper 32 bits of ``mhmpcounter31``            |
+---------+--------------------+--------+-----------------------------------------------+
|  0xF14  | ``mhartid``        | R      | Hardware Thread ID                            |
+---------+--------------------+--------+-----------------------------------------------+


Machine Status (mstatus)
------------------------

CSR Address: ``0x300``

Reset Value: ``0x0000_1800``

+-------+-----+---------------------------------------------------------------------------------+
| Bit#  | R/W | Description                                                                     |
+-------+-----+---------------------------------------------------------------------------------+
| 12:11 | R   | **MPP:** Statically 2'b11 and cannot be altered (read-only).                    |
+-------+-----+---------------------------------------------------------------------------------+
| 7     | RW  | **Previous Interrupt Enable (MPIE)**, i.e., before entering exception handling. |
+-------+-----+---------------------------------------------------------------------------------+
| 3     | RW  | **Interrupt Enable (MIE):** If set to 1'b1, interrupts are globally enabled.    |
+-------+-----+---------------------------------------------------------------------------------+

When an exception is encountered, ``mstatus``.MPIE will be set to ``mstatus``.MIE.
When the MRET instruction is executed, the value of MPIE will be stored back to ``mstatus``.MIE.

If you want to enable interrupt handling in your exception handler, set ``mstatus``.MIE to 1'b1 inside your handler code.


Machine ISA Register (misa)
---------------------------

CSR Address: ``0x301``

``misa`` is a WARL register which describes the ISA supported by the hart.
One Ibex, ``misa`` is hard-wired, i.e. it will remain unchanged after any write.


Machine Trap-Vector Base Address (mtvec)
----------------------------------------

CSR Address: ``0x305``

When an exception is encountered, the core jumps to the corresponding handler using the content of ``mtvec`` as base address.
It is a read-only register which contains the boot address.
``mtvec``.MODE is set to 2'b01 to indicate vectored interrupt handling.


Machine Exception PC (mepc)
---------------------------

CSR Address: ``0x341``

Reset Value: ``0x0000_0000``

When an exception is encountered, the current program counter is saved in ``mepc``, and the core jumps to the exception address.
When an MRET instruction is executed, the value from ``mepc`` replaces the current program counter.


Machine Cause (mcause)
----------------------

CSR Address: ``0x342``

Reset Value: ``0x0000_0000``

+-------+-----+------------------------------------------------------------------+
| Bit#  | R/W | Description                                                      |
+-------+-----+------------------------------------------------------------------+
| 31    | R   | **Interrupt:** This bit is set when the exception was triggered  |
|       |     | by an interrupt.                                                 |
+-------+-----+------------------------------------------------------------------+
| 4:0   | R   | **Exception Code**                                               |
+-------+-----+------------------------------------------------------------------+

When an exception is encountered, the corresponding exception code is stored in this register.


Machine Trap Value (mtval)
--------------------------

CSR Address: ``0x343``

Reset Value: ``0x0000_0000``

When an exception is encountered, this register can hold exception-specific information to assist software in handling the trap.

 * In the case of errors in the load-store unit ``mtval`` holds the address of the transaction causing the error.
 * If this transaction is misaligned, ``mtval`` holds the address of the missing transaction part.
 * In the case of illegal instruction exceptions, ``mtval`` holds the actual faulting instruction.

For all other exceptions, ``mtval`` is 0.


.. _csr-mhartid:

Hardware Thread ID (mhartid)
----------------------------

CSR Address: ``0xF14``

Reset Value: Defined

+-------+-----+------------------------------------------------------------------+
| Bit#  | R/W | Description                                                      |
+-------+-----+------------------------------------------------------------------+
| 10:5  | R   | **Cluster ID:** ID of the cluster                                |
+-------+-----+------------------------------------------------------------------+
| 3:0   | R   | **Core ID:** ID of the core within the cluster                   |
+-------+-----+------------------------------------------------------------------+
