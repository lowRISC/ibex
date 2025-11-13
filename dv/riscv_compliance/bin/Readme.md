# Pre-build SAIL RISC-V Model Binaries

SAIL RISC-V is the Golden reference model simulator for the formal specification of the RISC-V Architecture. The binaries are build by following the [instructions](https://riscof.readthedocs.io/en/stable/installation.html#install-plugin-models) available in RISCOF documentation. 

These binaries are build for both 32-bit and 64-bit architecture:

- `riscv_sim_RV32`
- `riscv_sim_RV64`

> :warning: SAIL model binaries must be available in the `$PATH` variable. To do that:
- Extract `sail-riscv.tar.gz` using
        
        tar -xzf sail-riscv.tar.gz sail-riscv
- Binaries will be extracted in the directory named `sail-riscv`. Export the path of this directory to `$PATH` variable

        export PATH=/path/to/sail-riscv:$PATH