# SymAFL v2 AFL++ custom mutator

This directory implements the current SymAFL v2 PCBT custom mutator.  It is
not the upstream SymSan task-generation/constraint-solving plugin: the v2
fuzzing path does not spawn a launcher sidecar, generate solving tasks, or
invoke Jigsaw or Z3.

For project setup and the complete local verification commands, see the
superproject [README](../../../README.md) and the documentation map under
[`docs/README.md`](../../../docs/README.md). Canonical current behavior is in
[`docs/system.md`](../../../docs/system.md),
[`docs/protocol.md`](../../../docs/protocol.md), and
[`docs/pcbt.md`](../../../docs/pcbt.md).

## Current execution model

PCBT mode requires two locally built target binaries, supplied through
`SYMAFL_CONCOLIC_TARGET` and `SYMAFL_CONCRETE_TARGET`:

1. AFL++ first starts the concolic target.  The `afl_custom_post_process`
   hook evaluates PCBT predicates and vetoes candidates that cannot reach a
   frontier; every admitted candidate executes with DFSan tracking.
2. Bootstrap reports every symbolic conditional event over a pipe and inserts
   the complete trace into PCBT (`pipe-full`).  AFL++ itself drains that pipe
   while waiting for the forkserver child.
3. After bootstrap, the admitted candidate reports only the suffix after its
   known frontier into bounded shared memory (`shm-suffix`).  The mutator adds
   this suffix only after AFL++ confirms a coverage gain.  If that buffer
   overflows, the same gaining input is replayed through the concolic
   forkserver with `pipe-suffix` and is then inserted.
4. When PCBT saturates, AFL++ stops the concolic forkserver, restarts the
   concrete target, retains the queue, rebuilds its coverage bitmap, and
   continues with ordinary AFL++ fuzzing.

The lifecycle, rather than `SYMAFL_TRACE_MODE`, selects transport mode.  The
environment variable is intentionally ignored if set.

## Source map

| File | Responsibility |
|---|---|
| `symsan.cpp` | AFL++ custom-mutator hooks, transport lifecycle, coverage-gain suffix handling |
| `pcbt.hpp`, `pcbt.cpp` | path-constraint binary tree, trace/suffix insertion, frontier screening |
| `pred.hpp`, `pred.cpp` | label-DAG conversion and conservative <=64-bit SMT bit-vector predicate interpreter |

Expressions outside the interpreter's supported domain (including wider
bit-vectors) are opaque and conservatively admitted, rather than truncated or
rejected.

## Regression coverage

Run from the superproject root after `scripts/build-all.sh`:

```bash
python3 tests/trace_check.py direct
python3 tests/trace_check.py afl
python3 tests/pcbt_pipe_check.py
python3 tests/pcbt_toy_modes_check.py
scripts/run-fuzz.sh pcbt
```

`pcbt_toy_modes_check.py` uses `tests/toy.c` with a one-event SHM capacity to
verify `pipe-full -> shm-suffix overflow -> pipe-suffix` without advancing to
the concrete phase.  The final smoke test verifies the PCBT-to-concrete phase
switch.
