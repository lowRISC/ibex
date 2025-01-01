Debug Tests
===========

Debugging requires many system components to all work together. The tests here
perform an end-to-end test, communicating with gdb and OpenOCD.
If a simulator or hardware passes all these tests, then you can be pretty
confident that the actual debug interface is functioning correctly.

Requirements
============
The following should be in the user's path:
* riscv64-unknown-elf-gcc (`rvv-0.9.x` branch for riscv-gnu-toolchain should
  work if master does not have vector support yet)
* riscv64-unknown-elf-gdb (can be overridden with `--gdb` when running
  gdbserver.py manually), which should be the latest from
  git://sourceware.org/git/binutils-gdb.git.
* spike (can be overridden with `--sim_cmd` when running gdbserver.py
  manually), which should be the latest from
  https://github.com/riscv/riscv-isa-sim.git.
* openocd (can be overridden with `--server_cmd` when running gdbserver.py
  manually), which should be the latest from
  https://github.com/riscv/riscv-openocd.git.

Usage
=====
To run a quick smoke test against spike, run `make`. For a more comprehensive
test against a variety of spike configurations, run `make all`.

To run tests against hardware, or a specific spike configuration, manually
invoke gdbserver.py: `./gdbserver.py targets/<file>.py`

You can run just a single test by specifying any part of its name on the
command line, eg: `./gdbserver.py targets/RISC-V/spike64.py S0` runs
SimpleS0Test.  Once that test has failed, you can look at the log file to get
an idea of what might have gone wrong.

For custom targets, you can create a .py file anywhere and pass its path on the
command line. The Targets class in `targets.py` contains documentation on what
every variable means.

Log Files
=========

All output from tests ends up in the `logs/` subdirectory, with one log file
per test. If a test fails, this is where to look.

Debug Tips
==========

You can see what spike is doing by adding `-l` to the spike command, eg.:
`./gdbserver.py --sim_cmd "$RISCV/bin/spike -l" targets/RISC-V/spike32.py Breakpoint`

You can see what OpenOCD is doing by adding `-d` to the OpenOCD command, eg.:
`./gdbserver.py --server_cmd "openocd -d" targets/RISC-V/spike32.py Breakpoint`

You can run gdb under valgrind by passing --gdb, eg.: `./gdbserver.py
--gdb "valgrind riscv64-unknown-elf-gdb" targets/RISC-V/spike64.py
DownloadTest`
