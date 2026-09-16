# ibex_branch_predict — Formal Verification

JasperGold module-level check for `ibex_branch_predict`.

## What is checked

`formal_tb.sv` contains two assertions and six cover points verified against
`ibex_branch_predict` for all reachable states:

| Property | Description |
|---|---|
| `predict_taken_matches_ref` | `predict_branch_taken_o` equals a golden-model decode of taken/not-taken for JAL, BRANCH, C.J, C.BRANCH — **proven** |
| `predict_target_matches_ref` | `predict_branch_pc_o` equals `fetch_pc_i + immediate` whenever the instruction is a branch or jump — **proven** |
| `BranchInsTypeOneHot` | JAL/BRANCH/C.J/C.BRANCH encodings never overlap (auto-generated from `unique case`) — **proven** |
| `jal_reachable` | COVER: a valid JAL instruction can be presented |
| `cj_reachable` | COVER: a valid compressed jump can be presented |
| `neg_branch_reachable` | COVER: a backward conditional branch can be presented |
| `pos_branch_reachable` | COVER: a forward conditional branch can be presented |
| `neg_cb_reachable` | COVER: a backward compressed branch can be presented |
| `pos_cb_reachable` | COVER: a forward compressed branch can be presented |

## Running

Requires Cadence JasperGold (`jg`) on `PATH` and the surrounding ibex repo
checkout (RTL is read from `../../rtl/` and `../../vendor/`). No FuseSoC or
other pre-build step is needed.

### From this directory

Enter the nix dev shell (checks that `jg` is on `PATH` and provides `make`):

```
nix develop .#formal   # enter the shell (or just `nix develop` for the default)
make batch             # headless proof, exits 0 on pass
make gui               # open JasperGold GUI
```

Without nix, ensure `jg` and `make` are on `PATH` and run `make batch` directly.

### From ibex/dv/formal/ (inside the ibex repo)

```
make branch-predictor
make branch-predictor-gui
```

### From the repo root (ibex_cheriot_verification)

```
make formal-branch-predictor
make formal-branch-predictor-gui
```

### From the repo root (via top-level Makefile)

```
make formal-branch-predictor
make formal-branch-predictor-gui
```

## Files

| File | Purpose |
|---|---|
| `check.tcl` | JasperGold script: analyze, elaborate, prove, cover |
| `formal_tb.sv` | Testbench module with assertions and cover points |
| `formal_tb_frag.svh` | One-liner instantiation fragment (used by alternative flows) |
| `branch_predict_bind.sv` | SV `bind` statement wiring `formal_tb` into `ibex_branch_predict` |
| `ibex_bp_fpv.core` | FuseSoC core for the SymbiYosys open-source flow |
| `Makefile` | Standalone targets: `batch`, `gui`, `clean` |

## Results

`run.log` and `results.txt` are written to this directory after each run.
The JasperGold project database lives in `jgproject/`.
