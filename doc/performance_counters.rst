.. _performance-counters:

Performance Counters
====================

Performance Counters in ZERO-RISCY are placed inside the Control and Status Registers and can be accessed with csrr and csrw instructions.


Performance Counter Mode Register (PCMR)
----------------------------------------

CSR Address: ``0x7A1``

Reset Value: ``0x0000_0003``

+-------+-----+------------------------------------------------------------------+
| Bit#  | R/W | Description                                                      |
+=======+=====+==================================================================+
| 1     | R/W | **Global Enable:** Activate/deactivate all performance counters. |
|       |     | If this bit is 0, all performance counters are disabled. After   |
|       |     | reset, this bit is set.                                          |
+-------+-----+------------------------------------------------------------------+
| 0     | R/W | **Saturation:** If this bit is set, saturating arithmetic is     |
|       |     | used in the performance counter counters. After reset, this bit  |
|       |     | is set.                                                          |
+-------+-----+------------------------------------------------------------------+


Performance Counter Event Register (PCER)
-----------------------------------------

CSR Address: ``0x7A0``

Reset Value: ``0x0000_0000``

+-------+-----+------------------------------------------------------------------+
| Bit#  | R/W | Description                                                      |
+=======+=====+==================================================================+
| 16    | R/W | **TCDM_CONT**                                                    |
+-------+-----+------------------------------------------------------------------+
| 15    | R/W | **ST_EXT_CYC**                                                   |
+-------+-----+------------------------------------------------------------------+
| 14    | R/W | **LD_EXT_CYC**                                                   |
+-------+-----+------------------------------------------------------------------+
| 13    | R/W | **ST_EXT**                                                       |
+-------+-----+------------------------------------------------------------------+
| 12    | R/W | **LD_EXT**                                                       |
+-------+-----+------------------------------------------------------------------+
| 11    | R/W | **DELAY_SLOT**                                                   |
+-------+-----+------------------------------------------------------------------+
| 10    | R/W | **BRANCH**                                                       |
+-------+-----+------------------------------------------------------------------+
| 9     | R/W | **JUMP**                                                         |
+-------+-----+------------------------------------------------------------------+
| 8     | R/W | **ST**                                                           |
+-------+-----+------------------------------------------------------------------+
| 7     | R/W | **LD**                                                           |
+-------+-----+------------------------------------------------------------------+
| 6     | R/W | **WBRANCH_CYC**                                                  |
+-------+-----+------------------------------------------------------------------+
| 5     | R/W | **WBRANCH**                                                      |
+-------+-----+------------------------------------------------------------------+
| 4     | R/W | **IMISS**                                                        |
+-------+-----+------------------------------------------------------------------+
| 3     | R/W | **RESERVED**                                                     |
+-------+-----+------------------------------------------------------------------+
| 2     | R/W | **RESERVED**                                                     |
+-------+-----+------------------------------------------------------------------+
| 1     | R/W | **INSTR**                                                        |
+-------+-----+------------------------------------------------------------------+
| 0     | R/W | **CYCLES**                                                       |
+-------+-----+------------------------------------------------------------------+

Each bit in the PCER register controls one performance counter. If the bit is 1, the counter is enabled and starts counting events. If it is 0, the counter is disabled and its value won’t change.

In the ASIC there is only one counter register, thus all counter events are masked by PCER and ORed together, i.e. if one of the enabled event happens, the counter will be increased. If multiple non-masked events happen at the same time, the counter will only be increased by one.
In order to be able to count separate events on the ASIC, the program can be executed in a loop with different events configured.

In the FPGA or RTL simulation version, each event has its own counter and can be accessed separately.

Performance Counter Counter Register (PCCR0-31)
-----------------------------------------------

CSR Address: ``0x780`` - ``0x79F``

Reset Value: ``0x0000_0000``

PCCR registers support both saturating and wrap-around arithmetic. This is controlled by the saturation bit in PCMR.

+----------+----------------+----------------------------------------------------------------+
| Register | Name           | Description                                                    |
+==========+================+================================================================+
| PCCR0    | **CYCLES**     | Counts the number of cycles the core was active (not sleeping) |
+----------+----------------+----------------------------------------------------------------+
| PCCR1    | **INSTR**      | Counts the number of instructions executed                     |
+----------+----------------+----------------------------------------------------------------+
| PCCR2    | **-**          | Reserved                                                       |
+----------+----------------+----------------------------------------------------------------+
| PCCR3    | **-**          | Reserved                                                       |
+----------+----------------+----------------------------------------------------------------+
| PCCR4    | **IMISS**      | Cycles waiting for instruction fetches, i.e. number of         |
|          |                | instructions wasted due to non-ideal caching                   |
+----------+----------------+----------------------------------------------------------------+
| PCCR5    | **LD**         | Number of data memory loads executed. Misaligned accesses are  |
|          |                | counted twice                                                  |
+----------+----------------+----------------------------------------------------------------+
| PCCR6    | **ST**         | Number of data memory stores executed. Misaligned accesses are |
|          |                | counted twice                                                  |
+----------+----------------+----------------------------------------------------------------+
| PCCR7    | **JUMP**       | Number of unconditional jumps (j, jal, jr, jalr)               |
+----------+----------------+----------------------------------------------------------------+
| PCCR8    | **BRANCH**     | Number of branches. Counts taken and not taken branches        |
+----------+----------------+----------------------------------------------------------------+
| PCCR9    | **BTAKEN**     | Number of taken branches.                                      |
+----------+----------------+----------------------------------------------------------------+
| PCCR10   | **RVC**        | Number of compressed instructions executed                     |
+----------+----------------+----------------------------------------------------------------+
| PCCR11   | **LD_EXT**     | Number of memory loads to EXT executed. Misaligned accesses    |
|          |                | are counted twice. Every non-TCDM access is considered         |
|          |                | external (PULP only)                                           |
+----------+----------------+----------------------------------------------------------------+
| PCCR12   | **ST_EXT**     | Number of memory stores to EXT executed. Misaligned accesses   |
|          |                | are counted twice. Every non-TCDM access is considered         |
|          |                | external (PULP only)                                           |
+----------+----------------+----------------------------------------------------------------+
| PCCR13   | **LD_EXT_CYC** | Cycles used for memory loads to EXT. Every non-TCDM access is  |
|          |                | considered external (PULP only)                                |
+----------+----------------+----------------------------------------------------------------+
| PCCR14   | **ST_EXT_CYC** | Cycles used for memory stores to EXT. Every non-TCDM access is |
|          |                | considered external (PULP only)                                |
+----------+----------------+----------------------------------------------------------------+
| PCCR15   | **TCDM_CONT**  | Cycles wasted due to TCDM/log-interconnect contention          |
|          |                | (PULP only)                                                    |
+----------+----------------+----------------------------------------------------------------+
| PCCR31   | **ALL**        | Special Register, a write to this register will set all        |
|          |                | counters to the supplied value                                 |
+----------+----------------+----------------------------------------------------------------+

In the FPGA, RTL simulation and Virtual-Platform there are individual counters for each event type, i.e. PCCR0-30 each represent a separate register. To save area in the ASIC, there is only one counter and one counter register. Accessing PCCR0-30 will access the same counter register in the ASIC. Reading/writing from/to PCCR31 in the ASIC will access the same register as PCCR0-30.

:numref:`pcer` shows how events are first masked with the PCER register and then ORed together to increase the one performance counter PCCR.

.. figure:: images/pcer.png
   :name: pcer

   Events and PCCR, PCMR and PCER on the ASIC.
