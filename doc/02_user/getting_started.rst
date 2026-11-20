.. _getting-started:

Getting Started with Ibex
=========================

The Ibex repository contains all the RTL needed to simulate and synthesize an Ibex core.
`FuseSoC <https://github.com/olofk/fusesoc>`_ core files list the RTL files required to build Ibex (see :file:`ibex_core.core`).
The core itself is contained in the :file:`rtl/` directory, though it utilizes some primitives found in the :file:`vendor/lowrisc_ip/` directory.
These primitives come from the `OpenTitan <https://github.com/lowrisc/opentitan>`_ project but are copied into the Ibex repository so the RTL has no external dependencies.
You may wish to replace these primitives with your own and some are only required for specific configurations.
See :ref:`integration-prims` for more information.

There are several paths to follow depending on what you wish to accomplish:

 * See :ref:`examples` for a basic simulation setup running the core in isolation and a simple FPGA system.
 * See :ref:`verification` to begin working with the DV flow.
 * See :ref:`core-integration` to integrate the Ibex core into your own design.
 * See :ref:`integration-fusesoc-files` for information on how to get a complete RTL file listing to build Ibex for use outside of FuseSoC based flows.

Common development tasks
------------------------

The top-level Makefile provides shortcuts for common build, simulation, and lint tasks.
Run these commands from the root of the Ibex repository after installing the tools listed in :doc:`system_requirements`.

To build and run the Verilator-based Simple System example with the default ``small`` Ibex configuration:

.. code-block:: bash

   make build-simple-system
   make run-simple-system

To build and run the control and status register (CSR) testbench with Verilator:

.. code-block:: bash

   make build-csr-test
   make run-csr-test

The following commands run commonly used checks:

.. code-block:: bash

   # Lint the core and instruction tracer RTL.
   make lint-core-tracing

   # Lint the Python utilities.
   make python-lint

   # Build the RISC-V compliance simulation target.
   make build-riscv-compliance

The RTL tasks use the ``small`` configuration by default.
Set ``IBEX_CONFIG`` to select another configuration from :file:`ibex_configs.yaml`, for example:

.. code-block:: bash

   make IBEX_CONFIG=maxperf build-simple-system

Use ``make test-cfg IBEX_CONFIG=<configuration>`` to display the FuseSoC options for a configuration.
The full UVM verification environment requires additional tools and is described in :ref:`verification`.
