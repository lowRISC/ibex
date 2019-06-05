.. _cs-registers:

Control and Status Registers
============================

Ibex implements all the Control and Status Registers (CSRs) listed in the following table according to the RISC-V Privileged Specification, draft version 1.11.

+---------+--------------------+--------+-----------------------------------------------+
| Address |   Name             | Access | Description                                   |
+=========+====================+========+===============================================+
|  0x300  | ``mstatus``        | WARL   | Machine Status                                |
+---------+--------------------+--------+-----------------------------------------------+
|  0x301  | ``misa``           | WARL   | Machine ISA and Extensions                    |
+---------+--------------------+--------+-----------------------------------------------+
|  0x305  | ``mtvec``          | WARL   | Machine Trap-Handler Base Address             |
+---------+--------------------+--------+-----------------------------------------------+
|  0x320  | ``mcountinhibit``  | RW     | Machine Counter-Inhibit Register              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x323  | ``mhpmevent3``     | WARL   | Machine Performance-Monitoring Event Selector |
+---------+--------------------+--------+-----------------------------------------------+
|     .             .               .                    .                              |
+---------+--------------------+--------+-----------------------------------------------+
|  0x33F  | ``mhpmevent31``    | WARL   | Machine performance-monitoring event selector |
+---------+--------------------+--------+-----------------------------------------------+
|  0x341  | ``mepc``           | RW     | Machine Exception Program Counter             |
+---------+--------------------+--------+-----------------------------------------------+
|  0x342  | ``mcause``         | RW     | Machine Trap Cause                            |
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

When an exception is encountered, MPIE will be set to MIE.
When the ``mret`` instruction is executed, the value of MPIE will be stored back to IE.

If you want to enable interrupt handling in your exception handler, set MIE to 1'b1 inside your handler code.


Machine Trap-Vector Base Address (mtvec)
----------------------------------------

CSR Address: ``0x305``

When an exception is encountered, the core jumps to the corresponding handler using the content of ``mtvec`` as base address.
It is a read-only register which contains the boot address.


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
