.. _cs-registers:

Control and Status Registers
============================

ZERO-RISCY does not implement all control and status registers specified in the RISC-V privileged specifications, but is limited to the registers that were needed for the PULP system. The reason for this is that we wanted to keep the footprint of the core as low as possible and avoid any overhead that we do not explicitly need.

.. tabularcolumns:: |p{1cm}|p{.6cm}|p{.6cm}|p{1cm}|p{1cm}|p{1.5cm}|p{1.2cm}|p{6cm}|

+----------------------------+--------+---------+--------+-----------------------------------+
| CSR Address                | Hex    | Name    | Access | Description                       |
+-------+-----+-----+--------+--------+---------+--------+-----------------------------------+
| 11:10 | 9:8 | 7:6 | 5:0    |        |         |        |                                   |
+=======+=====+=====+========+========+=========+========+===================================+
| 00    | 11  | 00  | 000000 | 0x300  | MSTATUS | R/W    | Machine Status                    |
+-------+-----+-----+--------+--------+---------+--------+-----------------------------------+
| 00    | 11  | 00  | 000101 | 0x305  | MTVEC   | R      | Machine Trap-Vector Base Address  |
+-------+-----+-----+--------+--------+---------+--------+-----------------------------------+
| 00    | 11  | 01  | 000001 | 0x341  | MEPC    | R/W    | Machine Exception Program Counter |
+-------+-----+-----+--------+--------+---------+--------+-----------------------------------+
| 00    | 11  | 01  | 000010 | 0x342  | MCAUSE  | R/W    | Machine Trap Cause                |
+-------+-----+-----+--------+--------+---------+--------+-----------------------------------+
| 01    | 11  | 00  | 0xxxxx | 0x780- | PCCRs   | R/W    | Performance Counter Counter       |
|       |     |     |        | 0x79F  |         |        | Registers                         |
+-------+-----+-----+--------+--------+---------+--------+-----------------------------------+
| 01    | 11  | 10  | 100000 | 0x7A0  | PCER    | R/W    | Performance Counter Enable        |
+-------+-----+-----+--------+--------+---------+--------+-----------------------------------+
| 01    | 11  | 10  | 100001 | 0x7A1  | PCMR    | R/W    | Performance Counter Mode          |
+-------+-----+-----+--------+--------+---------+--------+-----------------------------------+
| 11    | 11  | 00  | 010100 | 0xF14  | MHARTID | R      | Hardware Thread ID                |
+-------+-----+-----+--------+--------+---------+--------+-----------------------------------+


Machine Status (MSTATUS)
------------------------

CSR Address: ``0x300``

Reset Value: ``0x0000_1800``

+-------+-----+------------------------------------------------------------------+
| Bit#  | R/W | Description                                                      |
+-------+-----+------------------------------------------------------------------+
| 12:11 | R   | **MPP:** Statically 2’b11 and cannot be altered (read-only).     |
+-------+-----+------------------------------------------------------------------+
| 7     | R/W | **Previous Interrupt Enable:** When an exception is encountered, |
|       |     | MPIE will be set to IE. When the mret instruction is executed,   |
|       |     | the value of MPIE will be stored to IE.                          |
+-------+-----+------------------------------------------------------------------+
| 3     | R/W | **Interrupt Enable:** If you want to enable interrupt handling   |
|       |     | in your exception handler, set the Interrupt Enable to 1’b1      |
|       |     | inside your handler code.                                        |
+-------+-----+------------------------------------------------------------------+


Machine Trap-Vector Base Address (MTVEC)
----------------------------------------

CSR Address: ``0x305``

When an exception is encountered, the core jumps to the corresponding handler using the content of the MTVEC as base address. It is a read-only register  which contains the boot address.


Machine Exception PC (MEPC)
---------------------------

CSR Address: ``0x341``

Reset Value: ``0x0000_0000``

When an exception is encountered, the current program counter is saved in MEPC, and the core jumps to the exception address. When an mret instruction is executed, the value from MEPC replaces the current program counter.


Machine Cause (MCAUSE)
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

MHARTID
-------

CSR Address: ``0xF14``

Reset Value: Defined

+-------+-----+------------------------------------------------------------------+
| Bit#  | R/W | Description                                                      |
+-------+-----+------------------------------------------------------------------+
| 10:5  | R   | **Cluster ID:** ID of the cluster                                |
+-------+-----+------------------------------------------------------------------+
| 3:0   | R   | **Core ID:** ID of the core within the cluster                   |
+-------+-----+------------------------------------------------------------------+
