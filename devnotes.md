# Development Journal

## 2026-05-06

The repository started with `plan.md` only.  The first implementation step creates a Lake package pinned to Lean 4.29.1, because elan reports that toolchain as installed and active.  No third-party Lean, JavaScript, or Wasm dependencies were added.

The initial executable target is narrow by design.  It supports the checked Lean declaration `LeanExe.Examples.AsciiDigits.validate : ByteArray -> Bool`, lowers it to a byte-range validator, and emits a standalone Wasm module with `memory`, `alloc`, `reset`, and `validate` exports.  Wasm compilation from the generic report, monomorphization, and typeclass specialization remain unimplemented.

Authoritative references used:

| Topic | Reference |
| ----- | --------- |
| Installed Lean toolchain | `elan show` |
| Lake project syntax | `lake init LeanExe exe.lean` template in `/tmp/lake-template-check` |
| Lean `ByteArray` API | Local Lean `#check` commands against Lean 4.29.1 |
| WebAssembly binary encoding | WebAssembly Core Specification binary format |

Current plan:

- [x] Create a Lake package and project root.
- [x] Add a byte-array validator with a Lean soundness theorem.
- [x] Add a small core IR and evaluation semantics.
- [x] Add proof-erasure and lowering correctness lemmas for the first boundary.
- [x] Add a Wasm emitter for the lowered validator.
- [x] Add a Node host runner and fuzz differential harness.
- [x] Build the project with Lake: `lake build`.
- [x] Emit the report and Wasm module: `.lake/build/bin/lean-wasm emit --out build/validate.wasm`, `.lake/build/bin/lean-wasm wat --out build/validate.wat`, and `.lake/build/bin/lean-wasm report --out build/extraction-report.txt`.
- [x] Run Lean/Wasm differential tests: `node test/fuzz_validate.js build/validate.wasm 200`.

## 2026-05-06: Checked-Environment Report

The next implementation step adds `spec.md` and a checked-environment report path.  The report uses Lean’s `importModules` API, `Environment.find?`, `ConstantInfo`, and `Expr.getUsedConstants` from the installed Lean 4.29.1 toolchain.  It imports a compiled module, finds an entry constant, expands project-local dependencies by root namespace, and records external dependencies as a classified frontier.

The report does not claim generic compilation.  It classifies declarations so the next compiler step has concrete blockers rather than an unstructured failure.  The current classifier detects unsupported effects, higher-order argument types, polymorphic declarations, typeclass instance dependencies, external library operations, `unsafe`, `partial`, opaque constants, axioms, quotients, inductives, constructors, and recursors.

Commands run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm report --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validate --out build/env-report.txt`
- [x] `.lake/build/bin/lean-wasm report --module Main --entry main`

## 2026-05-06: Collatz Demo

`LeanExe.Examples.Collatz.steps : UInt64 -> UInt64` computes Collatz steps with a `10000`-step fuel bound.  The bound avoids `partial` recursion and avoids assuming the global Collatz conjecture.  The Wasm emitter has a second hand-written module path that exports `collatz_steps(n: i64) -> i64` and `collatz_bench(n: i64, iters: i64) -> i64` and uses only scalar locals.

Planned checks:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm collatz-emit --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm collatz-wat --out build/collatz.wat`
- [x] `.lake/build/bin/lean-wasm collatz-eval --input 27`
- [x] Run `build/collatz.wasm` with Wasmtime 36.0.9 from `/tmp`: `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_steps build/collatz.wasm 27`.

## 2026-05-06: Collatz Timing

OEIS A284668 lists `989345275647` as the smallest number below `10^12` with the largest total stopping time in that range.  A local arbitrary-precision check gives `1348` steps and a maximum trajectory value of `1219624271099764`, which fits in `UInt64`.

The timing comparison uses `collatz_bench(n, iters)`, which repeats the computation inside the Lean executable or inside the Wasm module and returns the sum of all step counts.  This avoids measuring one process start per Collatz sequence.  The Wasm runs used Wasmtime 36.0.9 with `XDG_CACHE_HOME=/tmp`.

Commands run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm collatz-emit --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 27 --iters 10000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 27 10000000`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 63728127 --iters 1000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 63728127 1000000`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 989345275647 --iters 1000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 989345275647 1000000`
