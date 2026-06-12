# Snippy YAML test scenarios

This directory contains llvm-snippy YAML scenarios used by the custom Ibex
Snippy flow.

The files are not independent DV infrastructure. They are input scenarios for
the flow described in:

```text
dv/uvm/core_ibex/README.md
dv/uvm/core_ibex/snippy_cmake/README.md
```

A typical run selects one or more layouts through `SNIPPY_TEST`:

```bash
make run_snippy \
  OUT=out \
  COV=1 \
  SIMULATOR=vcs \
  IBEX_CONFIG=opentitan \
  RV32ZC=ibex_pkg::RV32Zca \
  SNIPPY_ITERATIONS=3 \
  SNIPPY_TEST="layout_arith, jalr, rem_div"
```

The selector accepts several forms. For example, the file
`layout_arith.yaml` can be selected as:

```text
layout_arith
arith
layout_arith.yaml
```

## Common includes

Most layouts include one of the shared section descriptions:

```text
sections.yaml
sections_branches.yaml
```

These files describe the memory regions used by generated code. New tests should
normally reuse one of them unless the scenario needs a special memory layout.

Some layouts define their own `sections:` block directly. This is used when the
test needs tighter control over memory placement or region size, for example in
memory-hazard and stress scenarios.

## Test development history

The test set was developed incrementally. The first goal was to get a stable
baseline for the unprivileged ISA, then add scenarios that create specific
microarchitectural situations, and finally add directed tests for rare coverage
points.

The coverage values below are historical reference points from this development
process. They are not strict pass/fail targets: exact numbers can change with
Ibex configuration, tool versions, coverage exclusions, simulator version, and
the selected test subset.

## Stage 1: baseline arithmetic and logical instructions

The initial baseline test is:

```text
layout_arith.yaml
```

It generates a long linear instruction stream using arithmetic, logical,
compressed, and bitmanip instructions. The histogram is  uniform, so the
test quickly covers many instruction-level coverpoints.

At this stage the generated program does not intentionally create complex
control-flow, loops, function calls, or memory-access patterns. It is useful as a
simple baseline because it exercises many opcodes, but it does not strongly
exercise branch behavior, pipeline flushes, memory hazards, or cross coverage
that depends on microarchitectural state.

Historically, three runs of this baseline test reached approximately:

```text
Functional coverage: 68.57%
Line coverage:       78.46%
```

## Stage 2: basic hazard and control-flow scenarios

After the baseline arithmetic test, the next step was to add layouts that force
more interesting execution patterns.

### Arithmetic RAW hazards

```text
layout_arith_hazard.yaml
```

This layout keeps the arithmetic/bitmanip instruction focus, but restricts the
available register set with `reserved-regs-list`. With fewer registers available,
Snippy is more likely to generate dependency chains such as:

```asm
add  x1, x4, x3
sub  x4, x1, x5
and  x4, x4, x1
```

This helps exercise data-hazard and forwarding-related coverpoints.

### Memory hazards

```text
layout_memory_hazard.yaml
layout_sw_sh_sb.yaml
```

These layouts focus on load/store behavior. They restrict the register set and
use memory-heavy histograms to create repeated accesses and dependency patterns.

`layout_memory_hazard.yaml` also uses a small data region to increase the chance
of repeated accesses to nearby addresses.

`layout_sw_sh_sb.yaml` focuses on store variants, especially byte and halfword
stores.

### Branches and loops

```text
layout_arith_branches.yaml
layout_memory_ifs.yaml
layout_memory_fors.yaml
layout_memory_branches.yaml
```

These layouts add branch behavior on top of arithmetic or memory instruction
streams.

`layout_memory_fors.yaml` uses loop-oriented branch generation:

```yaml
branches:
  loop-ratio: 1
  max-depth:
    loop: 2
```

This is useful when the goal is to create loop nests while keeping them bounded.

`layout_memory_ifs.yaml` disables loop generation:

```yaml
branches:
  loop-ratio: 0
```

This is useful for acyclic conditional-control-flow scenarios.

### Burst memory access

```text
layout_memory_burst.yaml
```

This layout uses Snippy burst mode for load/store instructions. The idea is to
separate address preparation from the actual memory operations, so the generated
program contains dense bursts of memory accesses rather than a repeated
address-setup/access pattern.

### Calls and jumps

```text
layout_memory_calls.yaml
layout_jalr.yaml
layout_jumps.yaml
layout_compressed_jumps.yaml
layout_c_jal.yaml
```

These layouts target function calls, direct and indirect jumps, compressed jump
forms, and call-graph behavior.

`layout_memory_calls.yaml` uses a call graph with several internal functions.
The generated functions are arranged into an acyclic call graph, while call
frequency is controlled by the instruction histogram.

`layout_jalr.yaml` is focused on indirect jump/call behavior.

`layout_jumps.yaml` is a broader jump/control-flow layout and uses branch
configuration with loops disabled.

The compressed layouts focus on compressed jump and call encodings.

### Misaligned and constrained memory access

```text
layout_memory_access_ranges.yaml
```

This layout uses `access-ranges` to constrain generated memory accesses. The
range uses a stride and offsets that make it easier to generate misaligned
access scenarios.

### Self-modifying code

```text
layout_smc.yaml
```

This layout targets self-modifying code. It uses `smcgram` so Snippy inserts the
helper routines it needs for copying code from source to target and then
executing the modified code.

The layout also constrains branch behavior and code layout (specific range of
addresses for code parts to be put in), because SMC requires a code-layout-aware
configuration.

### Stress scenario

```text
layout_stress.yaml
```

This is a broad stress layout. It combines several mechanisms in one scenario:
custom sections, branches, call graph, access ranges, and a large instruction
histogram.

It is useful as a high-pressure mixed scenario, but it is less isolated than the
smaller directed layouts.

With the basic scenario set, historical results reached approximately:

```text
Functional coverage: 88.17%
Line coverage:       81.64%
```

## Stage 3: rare and directed coverage cases

The next stage added directed layouts for coverage points that are unlikely to
be hit reliably by broad random generation.

### Division and remainder corner cases

```text
layout_rem_div.yaml
```

This layout targets rare overflow and corner cases for `DIV` and `REM`.

It uses `operands-reinitialization` to force operands such as:

```text
0x80000000, -1
```

while still allowing uniformly generated values for the rest of the cases.

### Immediate logical corner cases

```text
layout_ori_andi_xori.yaml
```

This layout targets immediate logical instructions where particular immediate
and operand combinations are useful for coverage.

It uses both:

```text
operands-reinitialization
imm-hist
```

to steer `ORI`, `ANDI`, and `XORI` toward values such as `1` and `-1`.

### ALU and bitmanip corner cases

```text
layout_alu_corner.yaml
layout_bit_instr.yaml
```

These layouts steer ALU and bitmanip instructions toward specific operand
values.

`layout_alu_corner.yaml` includes directed values for division, remainder,
shifts, and other arithmetic/logic cases.

`layout_bit_instr.yaml` focuses on bitmanip instructions and useful operand
patterns, including one-hot-like values and other directed cases.

### CSR access

```text
layout_csr.yaml
```

This layout targets CSR instructions. It uses `imm-hist` to select `mstatus`
(`0x300`) for CSR accesses. This keeps the test focused on CSR encodings that
are meaningful for the current Ibex environment.

### Interrupt and exception-like scenarios

```text
layout_interrupts.yaml
layout_illegal.yaml
```

These layouts target trap/exception-related behavior.

`layout_interrupts.yaml` includes `EBREAK`/compressed `EBREAK`-style scenarios
and reserves `x4`, because the environment uses this register for
`kernel_stack_end`, which is needed by the trap handler.

`layout_illegal.yaml` calls an external hand-written assembly helper named
`illegal_opcodes`:

```yaml
call-graph:
  entry-point: SnippyFunction
  function-list:
    - name: SnippyFunction
      callees:
        - illegal_opcodes
    - name: illegal_opcodes
      external: true

histogram:
  - [JAL, 100.0]
```

The `illegal_opcodes` helper is implemented in:

```text
../asm_func/
```

It emits the required illegal instruction encodings directly. This approach is
used because not every illegal encoding is convenient to express as a normal
Snippy instruction histogram entry.

After adding the directed rare-case layouts, historical results reached
approximately:

```text
Functional coverage: 97.03%
Line coverage:       82.63%
```

The remaining uncovered functional points were mostly related to jump scenarios
that were not fully supported by Snippy at the time of this test set.

## Current layout groups

The current YAML files can be read as the following groups.

### Baseline and arithmetic

```text
layout_arith.yaml
layout_arith_hazard.yaml
layout_arith_branches.yaml
layout_alu_corner.yaml
layout_bit_instr.yaml
layout_ori_andi_xori.yaml
```

### Division/remainder and rare arithmetic

```text
layout_rem_div.yaml
```

### Memory

```text
layout_memory_hazard.yaml
layout_memory_burst.yaml
layout_memory_access_ranges.yaml
layout_memory_branches.yaml
layout_memory_calls.yaml
layout_memory_fors.yaml
layout_memory_ifs.yaml
layout_sw_sh_sb.yaml
```

### Control flow and compressed jumps

```text
layout_jumps.yaml
layout_jalr.yaml
layout_compressed_jumps.yaml
layout_c_jal.yaml
```

### CSR, traps, illegal instructions, SMC

```text
layout_csr.yaml
layout_interrupts.yaml
layout_illegal.yaml
layout_smc.yaml
```

### Mixed stress

```text
layout_stress.yaml
```

## Adding a new test

To add a new Snippy scenario:

1. Create a new file in this directory using the `layout_<name>.yaml` naming
   convention.
2. Reuse `sections.yaml` or `sections_branches.yaml` unless the test needs a
   custom memory layout.
3. Start from an existing layout that is close to the new target scenario.
4. Set `num-instrs` according to the scenario. Directed corner-case tests can be
   short; broad instruction-space tests are usually longer.
5. Add or tune one of the following mechanisms when needed:
   - `histogram` for opcode selection;
   - `reserved-regs-list` for dependency pressure and hazards;
   - `branches` for loops or acyclic conditional control flow;
   - `call-graph` for function-call scenarios;
   - `access-ranges` for constrained or misaligned memory access;
   - `operands-reinitialization` for directed operand values;
   - `imm-hist` for directed immediate values;
   - `smcgram` for self-modifying-code scenarios.
   - Or any other, based on official documentation https://syntacore.github.io/snippy/
6. Run the test through `SNIPPY_TEST`.

Example:

```bash
make run_snippy \
  OUT=out \
  COV=1 \
  SIMULATOR=vcs \
  IBEX_CONFIG=opentitan \
  RV32ZC=ibex_pkg::RV32Zca \
  SNIPPY_ITERATIONS=3 \
  SNIPPY_TEST="layout_my_new_test"
```

## Notes on seeds

The scenarios in this directory are intended to provide stable coverage without
requiring fixed Snippy seeds. The usual development flow is to make a scenario
directed enough that it hits the target coverage in a small number of runs.

Fixing a seed can still be useful for debugging or for reproducing a specific
failure, but the preferred coverage-closure approach is to encode the desired
behavior in the YAML configuration rather than depending on one lucky random
seed.