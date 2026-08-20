# SymAFL v2 AFL++ custom mutator

This directory implements the current SymAFL v2 SEDBT custom mutator and
`symafl-analyzer`. It is not the upstream SymSan task-generation/constraint-solving
plugin: the v2 fuzzing path does not spawn a launcher sidecar, generate solving
tasks, or invoke Jigsaw or Z3.

For project setup, complete local verification commands, and experiment design,
see the superproject [README](../../../README.md), the documentation map under
[`docs/README.md`](../../../docs/README.md), and
[`docs/evaluation.md`](../../../docs/evaluation.md). Canonical system behavior,
runtime workflow, and SEDBT semantics are in
[`docs/system.md`](../../../docs/system.md).

## Current execution model

ADR 0010: `symafl-analyzer` owns concolic + the writable SEDBT. The mutator is
the concrete fuzzer side. `SYMAFL_ANALYZER_SOCK` is required.

1. Analyzer `InsertTrace` of `-i`, then **TREE_READY**.
2. Fuzzer CheckInput of initial seeds (learn-gate / closures), **BOOTSTRAP_ACK**.
3. Concrete havoc. New simplify_trace on `fsrv_cov` (`cov_gain_cnt`) → optional
`fsrv_san`; CheckInput then LearnJob only on an unexplored frontier
(`learned=0`, or `2` if ring full).
4. Next `queue_get` of `learned=0` uses CheckSuffix; `learned=1` keeps SHM
   pointers to path-symbol set and RSan nodes (focus only if bug edge open).

Production default does not globally veto concrete (ADR 0009). Path-s
mutants skip concrete on parent-suffix replay or a filled first disagreement
(`SYMAFL_PATH_S_SCREEN`). `SYMAFL_MUT_PATH_S=0`/`off` skips path-s;
unset/`1`/`suffix` is suffix taint; `full` is root→terminal taint. An
explore mutant that changed a tainted GEP-index pin skips `fsrv_cov` and
runs `fsrv_san` (`SYMAFL_PATH_S_CONS_SAN`, once per GEP value; independent
of screen). Indcall/read-length pins go through cov. A
sanitizer crash peeks `fsrv_cov`; `fsrv_cov_miss` counts unique con_san
crashes whose simplify_trace was already seen on coverage. Canonical
counters are `[sedbt-mce]`. Focused mutation uses RSan closures from the live
tree SHM. `SYMAFL_MUT_CLOSURE=0` skips that side's
analyzer compute and fuzzer stats/mutation. `learned=1` uses stacked
`s_havoc` on the symbol set; AFL havoc+splice follows at
`SYMAFL_MUT_HAVOC_PCT` (default 25).

## Source map

| File | Responsibility |
|---|---|
| `symsan.cpp` | AFL++ custom-mutator hooks, analyzer client, focused mutation |
| `symafl_analyzer.cpp` | concolic + SEDBT writer |
| `sedbt.hpp`, `sedbt.cpp` | path-constraint binary tree, trace/suffix insertion, closures |
| `pred.hpp`, `pred.cpp` | label-DAG conversion and conservative <=64-bit SMT bit-vector predicate interpreter |
| `shm_sedbt.*`, `analyzer_client.*`, `analyzer_ipc.hpp` | live tree SHM and LearnJob IPC |

Expressions outside the interpreter's supported domain (including wider
bit-vectors) are opaque and conservatively admitted, rather than truncated or
rejected.

## Regression coverage

Run from the superproject root after `scripts/build-all.sh`:

```bash
python3 tests/w1_analyzer_smoke.py
python3 tests/w2_analyzer_smoke.py
python3 tests/w3_oob_closure_smoke.py
python3 tests/analyzer_san_smoke.py
python3 tests/p1_no_veto_smoke.py
scripts/run-fuzz.sh analyzer
```
