# RISC-V compliance check

Verify that Ibex conforms to the RISC-V specification by running a compliance
check.

Version 2 of [riscv-compliance](https://github.com/riscv/riscv-compliance)
started to integrate with [RISCOF](https://gitlab.com/incoresemi/riscof) and
aims to provide the new structure with [version
3](https://github.com/riscv/riscv-compliance/issues/165#issuecomment-760121860).

Each core provides a Python plugin which handles the required setup,
compilation and execution step. This plugin is invoked by RISCOF.

A simulation of [Ibex](../riscv_compliance/README.md) is used to execute the
instruction checks.

RISCOF is not yet finished, some checks will fail and the configuration
provided by [config.ini](config.ini) will only compare the output from Ibex
to a fixed reference.

## Run RISCOF RISC-V Compliance

### Requirements

In addition to [steps 0, 1 and
2](../riscv_compliance/README.md#how-to-run-risc-v-compliance-on-ibex) the
RISCOF package must be installed:

```sh
pip3 install --user -U riscof
```

### Running the checks

```sh
cd $IBEX_REPO_BASE
export RISCV_PREFIX=riscv32-unknown-elf-
export IBEX_SIMULATOR=$PWD/build/lowrisc_ibex_ibex_riscv_compliance_0.1/sim-verilator/Vibex_riscv_compliance
riscof run --config dv/riscof/config.ini  --suite /path/to/riscv-compliance/riscv-test-suite --no-browser
```

## Additional notes to the current status

### Changing the reference model

In order to compare the results produced by Ibex to another model the file
`config.ini` must be updated.

To use for example [Sail](https://github.com/rems-project/sail-riscv) update
and append with:

```
[RISCOF]
ReferencePlugin=sail_cSim
ReferencePluginPath=/path/to/sail_cSim

[sail_cSim]
pluginpath=/path/to/sail_cSim
```

### Failing checks

Due to some current restrictions in the test suite some checks fail:
- Branch and jump fail due to
  [memory size](https://github.com/riscv/riscv-compliance/issues/157)
  restrictions.
- Incorrect selection of
  [RV64](https://github.com/riscv/riscv-compliance/pull/168) tests.
- [break](https://github.com/riscv/riscv-compliance/issues/145)
- [ecall](https://github.com/riscv/riscv-compliance/issues/146)
- [misalign ldst](https://github.com/riscv/riscv-compliance/issues/147)
- [misalign jmp](https://github.com/riscv/riscv-compliance/issues/148)


### Restrictions

- Due to backwards compatibility riscv-compliance testsuite will report some
  [warnings](https://github.com/riscv/riscv-compliance/issues/169).
- Not compatible with
  [RV32E](https://github.com/riscv/riscv-compliance/issues/142).


### Future updates

When the riscv-compliance framework v1 is not longer used, the riscv-compliance
target can be changed and the memory can be moved to a more sensible location
(e.g. `0x8000_0000`).
