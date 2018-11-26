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

.. caution::

   The instruction fetch interface differs from the LSU interface in that the address can change
   while the request is valid. This is because it can update the instructions to fetch when a
   branch occurs. As depicted in :numref:`if_timing_difference` care has to be taken when
   working with the address. The data returned must of course match the address during the grant
   cycle.

   .. wavedrom::
      :name: if_timing_difference
      :caption: Memory transaction with wait states

      {"signal":
        [
          {"name": "clk", "wave": "p......"},
          {"name": "data_addr_o", "wave": "x===xxx", "data": ["Address", "Address", "Address"]},
          {"name": "data_req_o", "wave": "01..0.."},
          {"name": "data_gnt_i", "wave": "0..10.."}, 
          {"name": "data_rvalid_i", "wave": "0....10"},
          {"name": "data_rdata_i", "wave": "xxxxx=x", "data": ["RData"]}
        ],
        "config": { "hscale": 2 }
      }
