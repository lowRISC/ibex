.. _core-integration:

Core Integration
================

The main module is named ``ibex_core`` and can be found in ``ibex_core.sv``.
Below, the instantiation template is given and the parameters and interfaces are described.

Instantiation Template
----------------------

.. code-block:: verilog

  ibex_core #(
      .MHPMCounterNum   (8),
      .MHPMCounterWidth (40),
      .RV32E            (0),
      .RV32M            (1),
      .DmHaltAddr       (32'h1A110800),
      .DmExceptionAddr  (32'h1A110808)
  ) u_core (
      // Clock and reset
      .clk_i          (),
      .rst_ni         (),
      .test_en_i      (),

      // Configuration
      .core_id_i      (),
      .cluster_id_i   (),
      .boot_addr_i    (),

      // Instruction memory interface
      .instr_req_o    (),
      .instr_gnt_i    (),
      .instr_rvalid_i (),
      .instr_addr_o   (),
      .instr_rdata_i  (),

      // Data memory interface
      .data_req_o     (),
      .data_gnt_i     (),
      .data_rvalid_i  (),
      .data_we_o      (),
      .data_be_o      (),
      .data_addr_o    (),
      .data_wdata_o   (),
      .data_rdata_i   (),
      .data_err_i     (),

      // Interrupt inputs
      .irq_i          (),
      .irq_id_i       (),
      .irq_ack_o      (),
      .irq_id_o       (),

      // Debug interface
      .debug_req_i    (),

      // Special control signal
      .fetch_enable_i ()
  );

Parameters
----------

+-----------------------+-------------+------------+-----------------------------------------------------------------+
| Name                  | Type/Range  | Default    | Description                                                     |
+=======================+=============+============+=================================================================+
| ``MHPMCounterNum``    | int (0..29) | 8          | Number of performance monitor event counters                    |
+-----------------------+-------------+------------+-----------------------------------------------------------------+
| ``MHPMCounterWidth``  | int (64..32)| 40         | Bit width of performance monitor event counters                 |
+-----------------------+-------------+------------+-----------------------------------------------------------------+
| ``RV32E``             | bit         | 0          | RV32E mode enable (16 integer registers only)                   |
+-----------------------+-------------+------------+-----------------------------------------------------------------+
| ``RV32M``             | bit         | 1          | M(ultiply) extension enable                                     |
+-----------------------+-------------+------------+-----------------------------------------------------------------+
| ``DmHaltAddr``        | int         | 0x1A110800 | Address to jump to when entering debug mode                     |
+-----------------------+-------------+------------+-----------------------------------------------------------------+
| ``DmExceptionAddr``   | int         | 0x1A110808 | Address to jump to when an exception occurs while in debug mode |
+-----------------------+-------------+------------+-----------------------------------------------------------------+


Interfaces
----------

+-------------------------+-------------------------+-----+----------------------------------------+
| Signal(s)               | Width                   | Dir | Description                            |
+=========================+=========================+=====+========================================+
| ``clk_i``               | 1                       | in  | Clock signal                           |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``rst_ni``              | 1                       | in  |Active-low synchronous reset            |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``test_en_i``           | 1                       | in  | Test input, enables clock              |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``core_id_i``           | 4                       | in  | Core ID, usually static, can be read   |
|                         |                         |     | from :ref:`csr-mhartid` CSR            |
+-------------------------+-------------------------+-----+                                        +
| ``cluster_id_i``        | 6                       | in  |                                        |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``boot_adr_i``          | 32                      | in  | First program counter after reset      |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``instr_*``             | Instruction fetch interface, see :ref:`instruction-fetch`              |
+-------------------------+------------------------------------------------------------------------+
| ``data_*``              | Load-store unit interface, see :ref:`load-store-unit`                  |
+-------------------------+------------------------------------------------------------------------+
| ``irq_*``               | Interrupt interface, see :ref:`interrupts`                             |
+-------------------------+------------------------------------------------------------------------+
| ``debug_*``             | Debug interface, see :ref:`debug-support`                              |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``fetch_enable_i``      | 1                       | in  | Enable the core, won't fetch when 0    |
+-------------------------+-------------------------+-----+----------------------------------------+
