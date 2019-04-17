.. _debug-unit:

Debug Unit
==========

Ibex implements execution-based debug according to the RISC-V Debug Specification, version 0.13.

Interface
---------

+-------------------------+-----------+----------------------------------------------+
| Signal                  | Direction | Description                                  |
+=========================+===========+==============================================+
| ``debug_req_i``         | input     | Request to enter debug mode                  |
+-------------------------+-----------+----------------------------------------------+

Parameters
----------

+--------------------------------------------------------------------------------------------+
| Parameter                | Description                                                     |
+==========================+=================================================================+
| ``DM_HALT_ADDRESS``      | Address to jump to when entering debug mode                     |
+--------------------------+-----------------------------------------------------------------+
| ``DM_EXCEPTION_ADDRESS`` | Address to jump to when an exception occurs while in debug mode |
+--------------------------+-----------------------------------------------------------------+

``debug_req_i`` is the "debug interrupt", issued by the debug module when the core should enter debug mode.
