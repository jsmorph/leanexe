# Lean kernel checker: M0.0

This is the first executable checkpoint toward a full Lean kernel checker
implemented in LeanExe. It checks one rule for concrete universe levels:

    Sort u : Sort (u + 1)

`Sort.lean` defines `LeanExe.KernelCheck.checkSort`. Its two `UInt64`
arguments encode the universe level and its claimed type's universe level.

| Returned word | Meaning |
|---|---|
| 0 | The claimed type is the successor sort. |
| 1 | The claimed type is incorrect. |
| 2 | The successor exceeds this initial UInt64 representation. |

The function checks the representation boundary before addition. It never
accepts a wrapped successor. These words are function results, not shell
exit statuses. This checkpoint does not parse declarations, check proofs,
or implement symbolic universe parameters.

## Build and check

Use the repository's pinned tools and execution rules from `AGENTS.md` and
`DEVELOPING.md`. Install Wasmtime with `tools/download-wasmtime.sh`, then:

```sh
node test/kernel_sort.js
```

The focused driver builds the source checks and compiler, emits
`.lake/build/kernel-check/checker-m0-0.wasm`, and invokes it with caller-supplied
arguments. It checks small levels, the signed i64 boundary, the largest
representable successor, and overflow against both mathematical BigInt succession
and standard Lean evaluation of the same 32 inputs.
It fails if the returned word differs from the expected result.

`SortTest.lean` also checks the source function's boundary behavior and asks
Lean to validate `Sort 0 : Sort 1`, `Sort 1 : Sort 2`, and `Sort 2 : Sort 3`.
These are focused source checks, not a generic compiler-correctness theorem.

## Run the generated artifact

Once built, only the WASM file and Wasmtime are required:

```sh
build/tools/wasmtime/current/wasmtime run --invoke checkSort .lake/build/kernel-check/checker-m0-0.wasm 0 1
build/tools/wasmtime/current/wasmtime run --invoke checkSort .lake/build/kernel-check/checker-m0-0.wasm 0 0
build/tools/wasmtime/current/wasmtime run --invoke checkSort .lake/build/kernel-check/checker-m0-0.wasm 1 2
```

Expected results: `0`, `1`, and `0`. These accept `Prop : Type`, reject
`Prop : Prop`, and accept `Type : Type 1`.

Wasmtime's CLI accepts signed i64 arguments. To supply UInt64 maximum,
use its two's-complement spelling `-1`; `checkSort ... -1 0` returns `2`.
The regression driver converts boundary inputs automatically.

## Next checkpoint

M0.1 adds concrete universe `max` and `imax`. The complete handoff and later
milestones are in [the kernel checker plan](../../plans/lean-kernel-checker.md).
