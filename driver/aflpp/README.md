# SymAFL v2 AFL++ custom mutator

This directory implements the current SymAFL v2 PCBT custom mutator and
`symafl-worker`. It is not the upstream SymSan task-generation/constraint-solving
plugin: the v2 fuzzing path does not spawn a launcher sidecar, generate solving
tasks, or invoke Jigsaw or Z3.

For project setup, complete local verification commands, and experiment design,
see the superproject [README](../../../README.md), the documentation map under
[`docs/README.md`](../../../docs/README.md), and
[`docs/evaluation.md`](../../../docs/evaluation.md). Canonical system behavior,
runtime workflow, and PCBT semantics are in
[`docs/system.md`](../../../docs/system.md).

## Current execution model

ADR 0010: `symafl-worker` owns concolic + the writable SEDBT. The mutator is
the concrete fuzzer side. `SYMAFL_WORKER_SOCK` is required.

1. Worker `InsertTrace` of `-i`, then **TREE_READY**.
2. Fuzzer CheckInput of initial seeds (learn-gate / closures), **BOOTSTRAP_ACK**.
3. Concrete havoc. Coverage gain → LearnJob `{cand_idx, frontier, dir, skip_cnt}`.
4. Optional sanitizer forkserver re-executes the same gainers.

Production default does not veto concrete (ADR 0009). Focused mutation uses
RSan closures from the live tree SHM.

## Source map

| File | Responsibility |
|---|---|
| `symsan.cpp` | AFL++ custom-mutator hooks, worker client, focused mutation |
| `symafl_worker.cpp` | concolic + SEDBT writer |
| `pcbt.hpp`, `pcbt.cpp` | path-constraint binary tree, trace/suffix insertion, closures |
| `pred.hpp`, `pred.cpp` | label-DAG conversion and conservative <=64-bit SMT bit-vector predicate interpreter |
| `shm_sedbt.*`, `worker_client.*`, `worker_ipc.hpp` | live tree SHM and LearnJob IPC |

Expressions outside the interpreter's supported domain (including wider
bit-vectors) are opaque and conservatively admitted, rather than truncated or
rejected.

## Regression coverage

Run from the superproject root after `scripts/build-all.sh`:

```bash
python3 tests/w1_worker_smoke.py
python3 tests/w2_worker_smoke.py
python3 tests/w3_oob_closure_smoke.py
python3 tests/worker_san_smoke.py
python3 tests/p1_no_veto_smoke.py
scripts/run-fuzz.sh worker
```
