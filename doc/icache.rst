.. _icache:

Instruction Cache
=================
:file:`rtl/ibex_icache.sv.`

NOTE - This module is currently DRAFT

The optional Instruction Cache (I$) is designed to improve CPU performance in systems with high instruction memory latency.
The I$ integrates into the CPU by replacing the prefetch buffer, interfacing directly between the bus and IF stage.

For details of the memory and IF stage interfaces see :ref:`instruction-fetch`.


Configuration options
---------------------

The following table describes the available configuration parameters.

+-------------------------+-----------+-----------------------------------------------+
| Parameter               | Default   | Description                                   |
+=========================+===========+===============================================+
| ``BusWidth``            | ``32``    | Width of instruction bus. Note, this is fixed |
|                         |           | at 32 for Ibex at the moment.                 |
+-------------------------+-----------+-----------------------------------------------+
| ``CacheSizeBytes``      | ``4kB``   | Size of cache in bytes.                       |
+-------------------------+-----------+-----------------------------------------------+
| ``LineSize``            | ``64``    | The width of one cache line in bits.          |
|                         |           | Line sizes smaller than 64 bits may give      |
|                         |           | compilation errors.                           |
+-------------------------+-----------+-----------------------------------------------+
| ``NumWays``             | ``2``     | The number of ways.                           |
+-------------------------+-----------+-----------------------------------------------+
| ``SpecRequest``         | ``1'b0``  | When set, the system will attempt to          |
|                         |           | speculatively request data from memory in     |
|                         |           | parallel with the cache lookup. This can give |
|                         |           | improved performance for workloads which      |
|                         |           | cache poorly (at the expense of power).       |
|                         |           | When not set, only branches will make         |
|                         |           | speculative requests.                         |
+-------------------------+-----------+-----------------------------------------------+
| ``BranchCache``         | ``1'b0``  | When set, the cache will only allocate the    |
|                         |           | targets of branches + two subsequent cache    |
|                         |           | lines. This gives improved performance in     |
|                         |           | systems with moderate latency by not          |
|                         |           | polluting the cache with data that can be     |
|                         |           | prefetched instead.                           |
|                         |           | When not set, all misses are allocated.       |
+-------------------------+-----------+-----------------------------------------------+

Performance notes
-----------------

Note that although larger cache line sizes allow for better area efficiency (lower tagram area overhead), there is a performance penalty.
When the core branches to an address that is not aligned to the bottom of a cache line (and the request misses in the cache), the I$ will attempt to fetch this address first from the bus.
The I$ will then fetch the rest of the remaining beats of data in wrapping address order to complete the cache line (in order to allocate it to the cache).
While these lower addresses are being fetched, the core is starved of data.
Based on current experimental results, a line size of 64 bits gives the best performance.

In cases where the core branches to addresses currently being prefetched, the same line can end up allocated to the cache in multiple ways.
This causes a minor performance inefficiency, but should not happen often in practice.

RAM Arrangement
---------------

The data RAMs are arranged as a series of 32 bit banks, the number depending on the cache line width and number of ways.
Each group of banks forming a single way can be combined into wider RAM instances if required since they are always accessed together.

Indicative RAM sizes for common configurations are given in the table below:

+-------------------------+-----------------+-----------------+
| Cache config            | Tag RAMs        | Data RAMs       |
+=========================+=================+=================+
| 4kB, 2 way, 64bit line  | 2 x 256 x 21bit | 4 x 256 x 32bit |
+-------------------------+-----------------+-----------------+
| 4kB, 2 way, 128bit line | 2 x 128 x 21bit | 8 x 128 x 32bit |
+-------------------------+-----------------+-----------------+
| 4kB, 4 way, 64bit line  | 4 x 128 x 21bit | 8 x 128 x 32bit |
+-------------------------+-----------------+-----------------+

Sub Unit Description
--------------------

.. figure:: images/icache_block.svg
   :name: icache_block
   :align: center

   Instruction Cache Block Diagram

Prefetch Address
^^^^^^^^^^^^^^^^

The prefetch address is updated to the branch target on every branch.
This address is then updated in cache-line increments each time a cache lookup is issued to the cache pipeline.

Cache Pipeline
^^^^^^^^^^^^^^

The cache pipeline consists of two stages, IC0 and IC1.

In IC0, lookup requests are arbitrated against cache allocation requests.
Lookup requests have highest priority since they naturally throttle themselves as fill buffer resources run out.
The arbitrated request is made to the RAMs in IC0.

In IC1, data from the RAMs are available and the cache hit status is determined.
Hit data is multiplexed from the data RAMs based on the hitting way.
If there was a cache miss, the victim way is chosen pseudo-randomly using a counter.

Fill buffers
^^^^^^^^^^^^

The fill buffers perform several functions in the I$ and constitute most of it's complexity.

- Since external requests can be made speculatively in parallel with the cache lookup, a fill buffer must be allocated in IC0 to track the request.
- The fill buffers are used as data storage for hitting requests as well as for miss tracking so all lookup requests require a fill buffer.
- A fill buffer makes multiple external requests to memory to fetch the required data to fill a cache line (tracked via ``fill_ext_cnt_q``).
- Returning data is tracked via ``fill_rvd_cnt_q``.
Not all requests will fetch all their data, since requests can be cancelled due to a cache hit or an intervening branch.
- If a fill buffer has not made any external requests it will be cancelled by an intervening branch, if it has made requests then the requests will be completed and the line allocated.
- Beats of data are supplied to the IF stage, tracked via ``fill_out_cnt_q``.
- If the line is due to be allocated into the cache, it will request for arbitration once all data has been received.
- Once all required actions are complete, the fill buffer releases and becomes available for a new request.

Since requests can perform actions out of order (cache hit in the shadow of an outstanding miss), and multiple requests can complete at the same time, the fill buffers are not a simple FIFO.
Each fill buffer maintains a matrix of which requests are older than it, and this is used for arbitrating between the fill buffers.

Data output
^^^^^^^^^^^

.. figure:: images/icache_mux.svg
   :name: icache_mux
   :align: center

   Instruction Cache Data Multiplexing

Data supplied to the IF stage are multiplexed between cache-hit data, fill buffer data, and incoming memory data.
The fill buffers track which request should supply data, and where that data should come from.
Data from the cache and the fill buffers are of cache line width, which is multiplexed down to 32 bits and then multiplexed against data from the bus.

The fill buffers attempt to supply the relevant word of data to the IF stage as soon as possible.
Hitting requests will supply the first word directly from the RAMs in IC1 while demand misses will supply data directly from the bus.
The remaining data from hits is buffered in the fill buffer data storage and supplied to the IF stage as-required.

To deal with misalignment caused by compressed instructions, there is a 16bit skid buffer to store the upper halfword.

Cache invalidation
^^^^^^^^^^^^^^^^^^

After reset, and when requested by the core (due to a FENCE.I instruction), the whole cache is invalidated.
Requests are inserted to invalidate the tag RAM for all ways in each cache line in sequence.
While the invalidation is in-progress, lookups and instruction fetches can proceed, but nothing will be allocated to the cache.
