Core Integration
================

The main module is named ``zeroriscy_core`` and can be found in ``zeroriscy_core.sv``. In the following the instantiation template is given and the parameters and interfaces are described.

Instantiation Template
----------------------

.. code-block:: verilog

  zeroriscy_core
   #(.N_EXT_PERF_COUNTERS (0),
     .RV32E (0),
     .RV32M (1))
  u_core
    (// Clock and reset
     .clk_i (),
     .rst_ni (),
     .clock_en_i (),
     .test_en_i (),

     // Configuration
     .core_id_i (),
     .cluster_id_i (),
     .boot_addr_i (),

     // Instruction memory interface
     .instr_req_o (),
     .instr_gnt_i (),
     .instr_rvalid_i (),
     .instr_addr_o (),
     .instr_rdata_i (),

     // Data memory interface
     .data_req_o (),
     .data_gnt_i (),
     .data_rvalid_i (),
     .data_we_o (),
     .data_be_o (),
     .data_addr_o (),
     .data_wdata_o (),
     .data_rdata_i (),
     .data_err_i (),

     // Interrupt inputs
     .irq_i (),
     .irq_id_i (),
     .irq_ack_o (),
     .irq_id_o (),

     // Debug Interface
     .debug_req_i (),
     .debug_gnt_o (),
     .debug_rvalid_o (),
     .debug_addr_i (),
     .debug_we_i (),
     .debug_wdata_i (),
     .debug_rdata_o (),
     .debug_halted_o (),
     .debug_halt_i (),
     .debug_resume_i (),

     // Special control signal
     .fetch_enable_i (),

     // External performance counters
     .ext_perf_counters_i ()
    );

Parameters
----------

+-------------------------+-------------+---------+------------------------------------------------+
| Name                    | Type/Range  | Default | Description                                    |
+=========================+=============+=========+================================================+
| ``N_EXT_PERF_COUNTERS`` | int (0..21) | 0       | Number of external performance counters        |
+-------------------------+-------------+---------+------------------------------------------------+
| ``RV32E``               | int (0..1)  | 0       | RV32E mode enable (16 integer registers only)  |
+-------------------------+-------------+---------+------------------------------------------------+
| ``RV32M``               | int (0..1)  | 1       | M(ultiply) extension enable                    |
+-------------------------+-------------+---------+------------------------------------------------+

    
Interfaces
----------


+-------------------------+-------------------------+-----+----------------------------------------+
| Signal(s)               | Width                   | Dir | Description                            |
+=========================+=========================+=====+========================================+
| ``clk_i``               | 1                       | in  | Clock signal                           |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``rst_ni``              | 1                       | in  |Active-low synchronous reset            |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``clock_en_i``          | 1                       | in  | Clock gating input                     |
|                         |                         |     | (0: clock gated, 1: clock running)     |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``test_en_i``           | 1                       | in  | Test input, enables clock              |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``core_id_i``           | 4                       | in  | Core id, usually static, can be read   |
|                         |                         |     | from :ref:`csr-mhartid`                |
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
| ``debug_*``             | Debug interface, see :ref:`debug-unit`                                 |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``fetch_enable_i``      | 1                       | in  | Enable the core, won't fetch when 0    |
+-------------------------+-------------------------+-----+----------------------------------------+
| ``ext_perf_counters_i`` | ``N_EXT_PERF_COUNTERS`` | in  | External performance counter           |
+-------------------------+-------------------------+-----+----------------------------------------+



