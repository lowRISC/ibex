.. _instruction-fetch:

Instruction Fetch
=================

The instruction fetcher of the core is able to supply one instruction to the ID stage per cycle if the instruction cache or the instruction memory is able to serve one instruction per cycle. The instruction address must be half-word-aligned due to the support of compressed instructions. It is not possible to jump to instruction addresses that have the LSB bit set.

For optimal performance and timing closure reasons, a prefetcher is used which fetches instruction from the instruction memory, or instruction cache.

The following table describes the signals that are used to fetch instructions. This interface is a simplified version that is used by the LSU that is described in :ref:`load-store-unit`. The difference is that no writes are possible and thus it needs less signals.


.. tabularcolumns:: |p{4cm}|l|p{9cm}|

+-------------------------+-----------+-----------------------------------------------+
| Signal                  | Direction | Description                                   |
+=========================+===========+===============================================+
| ``instr_req_o``         | output    | Request ready, must stay high until           |
|                         |           | ``instr_gnt_i`` is high for one cycle         |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_addr_o[31:0]``  | output    | Address                                       |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_rdata_i[31:0]`` | input     | Data read from memory                         |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_rvalid_i``      | input     | ``instr_rdata_is`` holds valid data when      |
|                         |           | ``instr_rvalid_i`` is high. This signal will  |
|                         |           | be high for exactly one cycle per request.    |
+-------------------------+-----------+-----------------------------------------------+
| ``instr_gnt_i``         | input     | The other side accepted the request.          |
|                         |           | ``instr_addr_o`` may change in the next cycle |
+-------------------------+-----------+-----------------------------------------------+


Protocol
--------

The protocol used to communicate with the instruction cache or the instruction memory is the same as the protocol used by the LSU. See the description of the LSU in :ref:`LSU Protocol<lsu-protocol>` for details about the protocol.
