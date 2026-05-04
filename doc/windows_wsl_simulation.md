Documentation for issue #741:

---

## Running Ibex Simple System Simulation on Windows (via WSL)

This guide documents the steps and fixes required to run the Ibex Verilator simulation on a Windows machine using WSL (Windows Subsystem for Linux).

---

### Prerequisites

- Windows 10/11 with WSL installed
- Ubuntu 24.04 (Noble) inside WSL

---

### Step 1 — Install WSL

Open PowerShell as administrator:

```bash
wsl --install
```

Restart your machine. All following commands run inside WSL.

---

### Step 2 — Install system dependencies

```bash
sudo apt update
sudo apt install python3-venv python3-full verilator srecord \
  gcc-riscv64-unknown-elf git make
```

**Why `srecord`?** The build process uses `srec_cat` to convert the compiled binary into a `.vmem` memory file. Without it, the make step silently produces `.elf` and `.bin` but fails at the final conversion step.

**Why `riscv64` not `riscv32`?** Ubuntu 24 only ships `riscv64-unknown-elf-gcc`. It compiles 32-bit RISC-V code fine with the right flags. Create symlinks so the Makefile can find it:

```bash
sudo ln -s /usr/bin/riscv64-unknown-elf-gcc /usr/bin/riscv32-unknown-elf-gcc
sudo ln -s /usr/bin/riscv64-unknown-elf-objcopy /usr/bin/riscv32-unknown-elf-objcopy
sudo ln -s /usr/bin/riscv64-unknown-elf-objdump /usr/bin/riscv32-unknown-elf-objdump
```

---

### Step 3 — Set up Python virtual environment

Ubuntu 24 blocks system-wide pip installs. Use a venv instead:

```bash
python3 -m venv ~/vlsi-env
source ~/vlsi-env/bin/activate

pip install fusesoc edalize packaging
```

To activate automatically on every WSL startup:

```bash
echo "source ~/vlsi-env/bin/activate" >> ~/.bashrc
```

**Packages needed and why:**
- `fusesoc` — build system that orchestrates the simulation flow
- `edalize` — backend EDA tool abstraction layer (not pulled in automatically by fusesoc)
- `packaging` — version checking utility used by `check_tool_requirements.py` (not included by default)

---

### Step 4 — Clone the repo and set up remotes

```bash
# Fork lowRISC/ibex on GitHub first, then:
git clone https://github.com/YOUR_USERNAME/ibex.git
cd ibex

# Keep upstream as a remote to pull future updates
git remote rename origin upstream
git remote add origin https://github.com/YOUR_USERNAME/ibex.git
```

---

### Step 5 — Fix the GCC architecture flag

GCC 13.x (shipped with Ubuntu 24) requires CSR instructions to be explicitly declared via the `zicsr` extension. Without this fix you get errors like:

```
Error: unrecognized opcode `csrw mhpmcounter3h,x0', extension `zicsr' required
```

Edit `examples/sw/simple_system/common/common.mk`:

```bash
nano examples/sw/simple_system/common/common.mk
```

Find this line:

```makefile
ARCH ?= rv32imc
```

Change it to:

```makefile
ARCH ?= rv32imc_zicsr
```

Save with `Ctrl+O` → Enter → `Ctrl+X`.

---

### Step 6 — Build the test program

```bash
make -C examples/sw/simple_system/hello_test
```

Expected output files in `examples/sw/simple_system/hello_test/`:

```
hello_test.bin  hello_test.c  hello_test.d
hello_test.elf  hello_test.o  hello_test.vmem  Makefile
```

If `hello_test.vmem` is missing, `srecord` was not installed (see Step 2).

---

### Step 7 — Run the simulation

```bash
fusesoc --cores-root=. run --target=sim --tool=verilator \
  lowrisc:ibex:ibex_simple_system \
  --SRAMInitFile=$(pwd)/examples/sw/simple_system/hello_test/hello_test.vmem
```

**Note:** Use `$(pwd)` for an absolute path — relative paths are silently ignored and the CPU will loop on empty memory printing `Illegal instruction` indefinitely.

**Note:** The flag is `--SRAMInitFile`, not `--ram_init_file`.

---

### Expected successful output

```
Simulation of Ibex
==================
Initializing memory from file 'hello_test.vmem'
Terminating simulation by software request.
Received $finish() from Verilog, shutting down simulation.

Simulation statistics
=====================
Executed cycles:   13274
Wallclock time:    0.125 s
Instructions Retired: 261
```

---

### Known warnings (safe to ignore)

- **`WARNING: This backend is deprecated`** — edalize backend deprecation notice. The simulation still works. Migration to the Flow API is tracked separately.
- **`launch-ros requires setuptools`** — unrelated ROS package conflict, does not affect ibex.

---

