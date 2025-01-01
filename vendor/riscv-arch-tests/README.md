
# RISC-V Architecture Test SIG

This is a repository for the work of the RISC-V Foundation Architecture Test SIG. The repository owners are:

- Neel Gala (InCore Semiconductors)
- Marc Karasek (Inspire Semiconductors)

Quick Links:

  - Details of the RISC-V Foundation, the work of its task groups, and how to become a member can be found at [riscv.org](https://riscv.org/).
  - For more details and documentation on the current test environment see: [doc/README.adoc](doc/README.adoc)
  - For more details on the test format spec see: [spec/TestFormatSpec.adoc](spec/TestFormatSpec.adoc)
  - For contributions and reporting issues please refer to [CONTRIBUTION.md](CONTRIBUTION.md)
  - For more details on the usage of the current framework see : [RISCOF](https://riscof.readthedocs.io/)

**Note : The RISCOF framework requires a
[riscv-config](https://github.com/riscv-software-src/riscv-config) YAML to describe the
configurations implemented by the DUT**

## Old Framework

The older 2.x version of the framework (based on Makefiles) can be found in a separate branch :
[old-framework-2.x](https://github.com/riscv-non-isa/riscv-arch-test/tree/old-framework-2.x). This
branch is no longer officially supported and all changes must occur on the main branch.

## Test Disclaimers

The following are the exhaustive list of disclaimers that can be used as waivers by target owners 
when reporting the status of pass/fail on the execution of the architectural suite on their respective targets.

1. For the following set of misaligned-tests, signature mismatches will occur if misaligned accesses can sometimes succeed (without an exception) and sometimes fail on the DUT.

   1. rv32i_m/privilege/src/misalign-[lb[u],lh[u],lw,sh,sb,sw]-01.S
   2. rv64i_m/privilege/src/misalign-[lb[u],lh[u],lw[u],ld,sb,sh,sw,sd]-01.S

3. The machine mode trap handler used in the privilege tests assumes one of the following conditions. 
   Targets not satisfying any of the following conditions are bound to fail the entire 
   rv32i_m/privilege and rv64i_m/privilege tests:
   1. The target must have implemented mtvec which is completely writable by the test in machine mode.
   2. The target has initialized mtvec, before entering the test (via RVMODEL_BOOT), to point to a memory location which has both read and write permissions.

## Test Stats

The coverage and data propogation statistics of each test are hosted on
[Google-Drive](https://drive.google.com/drive/folders/1KBRy6OgxnOPTDgyfJDj0gcMi5VdMLtVo?usp=share_link) for reference. This to avoid bloating this repo in size.

## Contribution process

Please refer to to [CONTRIBUTION.md](CONTRIBUTION.md) for guidelines on contributions.

## Licensing

In general:
- code is licensed under one of the following:
  - the BSD 3-clause license (SPDX license identifier `BSD-3-Clause`);
  - the Apache License (SPDX license identifier `Apache-2.0`); while
- documentation is licensed under the Creative Commons Attribution 4.0 International license (SPDX license identifier `CC-BY-4.0`).

The files [`COPYING.BSD`](./COPYING.BSD), [`COPYING.APACHE`](./COPYING.APACHE) and [`COPYING.CC`](./COPYING.CC) in the top level directory contain the complete text of these licenses.

## Engineering practice

- Documentation uses the structured text format _AsciiDoc_.  See [`doc/README.adoc`](doc/README.adoc) for more details.

- Some directories use `ChangeLog` files to track changes in the code and documentation.  Please honor these, keeping them up to date and including the ChangeLog entry in the _git_ commit message.

- Please include a comment with the SPDX license identifier in all source files, for example:
```
// SPDX-License-Identifier: BSD-3-Clause
```

## Quick Links:

- RISCOF \[[DOCS](https://riscof.readthedocs.io/en/latest/)\] \[[REPO](https://github.com/riscv-software-src/riscof)\]: This is the next version of the architectural test framework currently under development
- RISCV-ISAC \[[DOCS](https://riscv-isac.readthedocs.io/en/latest/index.html)\] \[[REPO](https://github.com/riscv-software-src/riscv-isac)\] : This is an ISA level coverage extraction tool for RISC-V which used to generate the coverage statistics of the architectural tests.
- RISCV-CTG: \[[DOCS](https://riscv-ctg.readthedocs.io/en/latest/index.html)\]\[[REPO](https://github.com/riscv-software-src/riscv-ctg)\]: This is a RISC-V Architectural Test generator used to generate some of the tests already checked into this repository.
- [Videos](https://youtu.be/VIW1or1Oubo): This Global Forum 2020 video provides an introduction to the above mentioned tools
- [riscvOVPsim](https://github.com/riscv-ovpsim/imperas-riscv-tests): Imperas freeware RISC-V reference simulator for compliance testing
- [riscvOVPsimPlus](https://www.ovpworld.org/riscvOVPsimPlus/): Imperas enhanced freeware RISC-V reference simulator for test development and verification

