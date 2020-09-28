.. _core-integration:

Core Integration
================

The main module is named :verilog:ref:`ibex_core` and can be found in :file:`ibex_core.sv`.
Below, the instantiation template is given and the parameters and interfaces are described.


Parameters
----------

.. verilog:parameter:: parameter bit PMPEnable = 0

  Enable PMP support

.. verilog:parameter:: parameter int unsigned PMPGranularity = 0

  Minimum granularity of PMP address matching.

  Valid data range: 0..31

.. verilog:parameter:: parameter int unsigned PMPNumRegions = 4

  Number implemented PMP regions (ignored if PMPEnable == 0).

  Valid data range: 1..16

.. verilog:parameter:: parameter int unsigned MHPMCounterNum = 0

  Number of performance monitor event counters.

  Valid data range: 0..10

.. verilog:parameter:: parameter int unsigned MHPMCounterWidth = 40

  Bit width of performance monitor event counters.

  Valid data range: 64..1

.. verilog:parameter:: parameter bit RV32E = 0

  RV32E mode enable (16 integer registers only).

.. verilog:parameter:: parameter ibex_pkg::rv32m_e RV32M = RV32MFast

  M(ultiply) extension select:

  * ``ibex_pkg::RV32MNone``: No M-extension
  * ``ibex_pkg::RV32MSlow``: Slow multi-cycle multiplier, iterative divider
  * ``ibex_pkg::RV32MFast``: 3-4 cycle multiplier, iterative divider
  * ``ibex_pkg::RV32MSingleCycle``: 1-2 cycle multiplier, iterative divider

.. verilog:parameter:: parameter ibex_pkg::rv32b_e RV32B = RV32BNone

  B(itmanipulation) extension select:

  * ``ibex_pkg::RV32BNone``: No B-extension
  * ``ibex_pkg::RV32BBalanced``: Sub-extensions Zbb, Zbs, Zbf and Zbt
  * ``ibex_pkg::RV32Full``: All sub-extensions

.. verilog:parameter:: parameter ibex_pkg::regfile_e RegFile = RegFileFF

  Register file implementation select:

  * ``ibex_pkg::RegFileFF``: Generic flip-flop-based register file
  * ``ibex_pkg::RegFileFPGA``: Register file for FPGA targets
  * ``ibex_pkg::RegFileLatch``: Latch-based register file for ASIC targets

.. verilog:parameter:: parameter bit DbgTriggerEn = 0

  Enable debug trigger support (one trigger only)

.. verilog:parameter:: parameter int unsigned DmHaltAddr = 32'h1A110800

  Address to jump to when entering Debug Mode

.. verilog:parameter:: parameter int unsigned DmExceptionAddr = 32'h1A110808

  Address to jump to when an exception occurs while in Debug Mode

.. verilog:parameter:: parameter bit BranchTargetALU = 0

  *EXPERIMENTAL* - Enables branch target ALU removing a stall cycle from taken branches

.. verilog:parameter:: parameter bit WritebackStage = 0

  *EXPERIMENTAL* - Enables third pipeline stage (writeback) improving performance of loads and stores

.. verilog:parameter:: parameter bit ICache = 0

  *EXPERIMENTAL* Enable instruction cache instead of prefetch buffer

.. verilog:parameter:: parameter bit SecureIbex = 0

  *EXPERIMENTAL* Enable various additional features targeting secure code execution.

Ports
-----

Clock and reset
~~~~~~~~~~~~~~~

.. verilog:port:: input logic clk_i

  Clock signal

.. verilog:port:: input logic rst_ni

  Active-low asynchronous reset

.. verilog:port:: input logic test_en_i

  Test input, enables clock

.. verilog:port:: input logic fetch_enable_i

  When it comes out of reset, the core will not start fetching and executing instructions until it sees this pin set to 1'b1.
  Once started, it will continue until the next reset, regardless of the value of this pin.

.. verilog:port:: output logic core_sleep_o

  Core in WFI with no outstanding data or instruction accesses.
  Deasserts if an external event (interrupt or debug req) wakes the core up

Configuration
~~~~~~~~~~~~~

Ibex provides two ports for run-time configuration.
In most usage scenarios, however, these signals are set to constants at synthesis time.

.. verilog:port:: input  logic [31:0] hart_id_i

  Hart ID, usually static, can be read from :ref:`csr-mhartid` CSR

.. verilog:port:: input  logic [31:0] boot_addr_i

  First program counter after reset = ``boot_addr_i`` + 0x80, see :ref:`exceptions-interrupts`

Instruction fetch interface
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The instruction fetch interface connects Ibex with the instruction memory.
Refer to the :ref:`instruction-fetch` section for more information on this interface.

.. verilog:port:: output logic instr_req_o

  Request valid, must stay high until :verilog:ref:`instr_gnt_i` is high for one cycle

.. verilog:port:: input  logic instr_gnt_i

  The other side accepted the request.
  :verilog:ref:`instr_req_o` may be deasserted in the next cycle.

.. verilog:port:: input  logic instr_rvalid_i

  :verilog:ref:`instr_rdata_i` holds valid data when :verilog:ref:`instr_rvalid_i` is high.
  This signal will be high for exactly one cycle per request.

.. verilog:port:: output logic [31:0] instr_addr_o

  Address, word aligned

.. verilog:port:: input  logic [31:0] instr_rdata_i

  Data read from memory

.. verilog:port:: input  logic instr_err_i

  Memory access error

Load-store unit interface
~~~~~~~~~~~~~~~~~~~~~~~~~

The Load-Store Unit (LSU) of the core takes care of accessing the data memory.
Refer to the :ref:`load-store-unit` section for details.

.. verilog:port:: output logic data_req_o

  Request valid, must stay high until ``data_gnt_i`` is high for one cycle

.. verilog:port:: input  logic data_gnt_i

  The other side accepted the request.
  Outputs may change in the next cycle.

.. verilog:port:: input  logic data_rvalid_i

  ``data_err_i`` and ``data_rdata_i`` hold valid data when ``data_rvalid_i`` is high.
  This signal will be high for exactly one cycle per request.

.. verilog:port:: output logic data_we_o

  Write Enable, high for writes, low for reads. Sent together with ``data_req_o``

.. verilog:port:: output logic [3:0]  data_be_o

  Byte Enable. Is set for the bytes to write/read, sent together with ``data_req_o``

.. verilog:port:: output logic [31:0] data_addr_o

  Address, word aligned

.. verilog:port:: output logic [31:0] data_wdata_o

  Data to be written to memory, sent together with ``data_req_o``

.. verilog:port:: input  logic [31:0] data_rdata_i

  Data read from memory

.. verilog:port:: input  logic    data_err_i

  Error response from the bus or the memory:
  request cannot be handled. High in case of an error

Interrupt inputs
~~~~~~~~~~~~~~~~

Ibex implements trap handling for interrupts and exceptions according to the RISC-V Privileged Specification
Refer to the section :ref:`exceptions-interrupts` for details.

.. verilog:port:: input  logic irq_software_i

  Connected to memory-mapped (inter-processor) interrupt register

.. verilog:port:: input  logic irq_timer_i

  Connected to timer module

.. verilog:port:: input  logic irq_external_i

  Connected to platform-level interrupt controller

.. verilog:port:: input  logic [14:0] irq_fast_i

  15 fast, local interrupts

.. verilog:port:: input  logic irq_nm_i

  Non-maskeable interrupt.


Debug interface
~~~~~~~~~~~~~~~

Ibex contains logic to support run-control debugging according to the RISC-V Debug Specification.
Refer to the :ref:`debug-support` section for details.

.. verilog:port:: input  logic debug_req_i

  Request to enter Debug Mode

Security-related signals
~~~~~~~~~~~~~~~~~~~~~~~~

Ibex' security features can detect various security-related problems and produce alerts.
Refer to the :ref:`security` section for details.

.. verilog:port:: output logic alert_minor_o

  Core has detected a fault which it can safely recover from.
  Can be used by a system to log errors over time and detect tampering / attack.
  This signal is a pulse, one cycle per alert.

.. verilog:port:: output logic alert_major_o

  Core has detected a fault which cannot be recovered from.
  Can be used by a system to reset the core and possibly take other remedial action.
  This signal is a pulse, but might be set for multiple cycles per alert.

RISC-V Formal interface
~~~~~~~~~~~~~~~~~~~~~~~

The RISC-V Formal interface is a set of ports which provides internal processor state to simulation and verification environments.
The `RISC-V Formal Interface (RVFI) <https://github.com/SymbioticEDA/riscv-formal/blob/master/docs/rvfi.md>`_ specification describes the semantics of the individual ports in more detail.

.. note::

  The ports related to the RISC-V Formal Interface do not comply with the coding standards of ``_i``/``_o`` suffixes, but follow the convention of RISC-V Formal Interface Specification.

These ports are only available when the ``RVFI`` define is set.

.. verilog:port:: output logic    rvfi_valid
.. verilog:port:: output logic [63:0] rvfi_order
.. verilog:port:: output logic [31:0] rvfi_insn
.. verilog:port:: output logic rvfi_trap
.. verilog:port:: output logic    rvfi_halt
.. verilog:port:: output logic    rvfi_intr
.. verilog:port:: output logic [ 1:0] rvfi_mode
.. verilog:port:: output logic [ 1:0] rvfi_ixl
.. verilog:port:: output logic [ 4:0] rvfi_rs1_addr
.. verilog:port:: output logic [ 4:0] rvfi_rs2_addr
.. verilog:port:: output logic [ 4:0] rvfi_rs3_addr
.. verilog:port:: output logic [31:0] rvfi_rs1_rdata
.. verilog:port:: output logic [31:0] rvfi_rs2_rdata
.. verilog:port:: output logic [31:0] rvfi_rs3_rdata
.. verilog:port:: output logic [ 4:0] rvfi_rd_addr
.. verilog:port:: output logic [31:0] rvfi_rd_wdata
.. verilog:port:: output logic [31:0] rvfi_pc_rdata
.. verilog:port:: output logic [31:0] rvfi_pc_wdata
.. verilog:port:: output logic [31:0] rvfi_mem_addr
.. verilog:port:: output logic [ 3:0] rvfi_mem_rmask
.. verilog:port:: output logic [ 3:0] rvfi_mem_wmask
.. verilog:port:: output logic [31:0] rvfi_mem_rdata
.. verilog:port:: output logic [31:0] rvfi_mem_wdata



Instantiation Template
----------------------

.. code-block:: verilog

  ibex_core #(
      .PMPEnable        ( 0                   ),
      .PMPGranularity   ( 0                   ),
      .PMPNumRegions    ( 4                   ),
      .MHPMCounterNum   ( 0                   ),
      .MHPMCounterWidth ( 40                  ),
      .RV32E            ( 0                   ),
      .RV32M            ( ibex_pkg::RV32MFast ),
      .RV32B            ( ibex_pkg::RV32BNone ),
      .RegFile          ( ibex_pkg::RegFileFF ),
      .ICache           ( 0                   ),
      .ICacheECC        ( 0                   ),
      .BranchPrediction ( 0                   ),
      .SecureIbex       ( 0                   ),
      .DbgTriggerEn     ( 0                   ),
      .DmHaltAddr       ( 32'h1A110800        ),
      .DmExceptionAddr  ( 32'h1A110808        )
  ) u_core (
      // Clock and reset
      .clk_i          (),
      .rst_ni         (),
      .test_en_i      (),

      // Configuration
      .hart_id_i      (),
      .boot_addr_i    (),

      // Instruction memory interface
      .instr_req_o    (),
      .instr_gnt_i    (),
      .instr_rvalid_i (),
      .instr_addr_o   (),
      .instr_rdata_i  (),
      .instr_err_i    (),

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
      .irq_software_i (),
      .irq_timer_i    (),
      .irq_external_i (),
      .irq_fast_i     (),
      .irq_nm_i       (),

      // Debug interface
      .debug_req_i    (),

      // Special control signals
      .fetch_enable_i (),
      .alert_minor_o  (),
      .alert_major_o  (),
      .core_sleep_o   ()
  );
