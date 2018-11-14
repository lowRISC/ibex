.. _register-file:

Register File
=============

ZERO-RISCY has 31 or 15 32-bit wide registers depending if the RV32E extension is enabled. Register x0 is statically bound to 0 and can only be read, it does not contain any sequential logic.

There are two flavors of register file available:

1. Latch-based
2. Flip-flop based

While the latch-based register file is recommended for ASICs, the flip-flop based register file is recommended for FPGA synthesis, although both are compatible with either synthesis target. Note the flip-flop based register file is significantly larger than the latch-based register-file for an ASIC implementation.

Latch-based Register File
-------------------------

The latch based register file contains manually instantiated clock gating cells to keep the clock inactive when the latches are not written.

It is assumed that there is a clock gating cell for the target technology that is wrapped in a module called ``cluster_clock_gating`` and has the following ports:

* ``clk_i``: Clock Input
* ``en_i``: Clock Enable Input
* ``test_en_i``: Test Enable Input (activates the clock even though en_i is not set)
* ``clk_o``: Gated Clock Output
