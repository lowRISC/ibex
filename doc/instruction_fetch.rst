.. _instruction-fetch:

Instruction Fetch
=================

The Instruction-Fetch (IF) stage of the core is able to supply one instruction to the Instruction-Decode (ID) stage per cycle if the instruction cache or the instruction memory is able to serve one instruction per cycle.
For optimal performance and timing closure reasons, a prefetcher is used which fetches instructions from the instruction memory, or instruction cache.

The following table describes the signals that are used to fetch instructions.
This interface is a simplified version of the interface used on the data interface as described in :ref:`load-store-unit`.
The main difference is that the instruction interface does not allow for write transactions and thus needs less signals.

.. tabularcolumns:: |p{4cm}|l|p{9cm}|

+-------------------------+-----------+-----------------------------------------------+
| Signal                  | Direction | Description                                   |
+=========================+===========+===============================================+
| ``instr_req_o``         | output    | Request valid, must stay high until           |
|                         |           | ``instr_gnt_i`` is high for one cycle         |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_addr_o[31:0]``  | output    | Address, word aligned                         |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_gnt_i``         | input     | The other side accepted the request.          |
|                         |           | ``instr_req_o`` may be deasserted in the next |
|                         |           | cycle.                                        |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_rvalid_i``      | input     | ``instr_rdata_i`` holds valid data when       |
|                         |           | ``instr_rvalid_i`` is high. This signal will  |
|                         |           | be high for exactly one cycle per request.    |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_rdata_i[31:0]`` | input     | Data read from memory                         |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_err_i``         | input     | Memory access error                           |
+-------------------------+-----------+-----------------------------------------------+


Misaligned Accesses
-------------------

Externally, the IF interface performs word-aligned instruction fetches only.
Misaligned instruction fetches are handled by performing two separate word-aligned instruction fetches.
Internally, the core can deal with both word- and half-word-aligned instruction addresses to support compressed instructions.
The LSB of the instruction address is ignored internally.


Protocol
--------

The protocol used to communicate with the instruction cache or the instruction memory is very similar to the protocol used by the LSU on the data interface of Ibex.
See the description of the LSU in :ref:`LSU Protocol<lsu-protocol>` for details about this protocol.

