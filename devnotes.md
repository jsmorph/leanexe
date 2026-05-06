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

`LeanExe.Examples.Collatz.steps : UInt64 -> UInt64` computes Collatz steps with a `10000`-step fuel bound.  The bound avoids `partial` recursion and avoids assuming the global Collatz conjecture.  The first Collatz Wasm emitter used a Collatz-specific byte emitter.  That path was removed.  The current path uses `lean-wasm compile --module <module> --entry <name> --out <path>`, which loads checked declarations, extracts the supported first `UInt64` fragment into `LeanExe.IR.Core`, and emits Wasm from that IR.

Planned checks:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wat`
- [x] `.lake/build/bin/lean-wasm collatz-eval --input 27`
- [x] Run `build/collatz.wasm` with Wasmtime 36.0.9 from `/tmp`: `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_steps build/collatz.wasm 27`.

Current limitation: the generic compiler fragment supports only monomorphic first-order functions returning `UInt64`, `UInt64` and bounded `Nat` parameters represented as Wasm `i64`, primitive arithmetic, direct calls, `if`, boolean equality and disjunction, and tail recursion over a decreasing `Nat` fuel argument.  It does not lower arbitrary Lean expressions, data structures, pattern matching over user inductives, arrays, byte arrays, typeclasses beyond the primitive patterns it recognizes, or IO.  `compile-wat` prints WAT from the same IR used by binary emission.  The verification pass compared Lean and Wasmtime for `27`, `989345275647`, `bench 27 10`, and `bench 989345275647 3`.

## 2026-05-06: Collatz Timing

OEIS A284668 lists `989345275647` as the smallest number below `10^12` with the largest total stopping time in that range.  A local arbitrary-precision check gives `1348` steps and a maximum trajectory value of `1219624271099764`, which fits in `UInt64`.

The timing comparison used `collatz_bench(n, iters)`, which repeats the computation inside the Lean executable or inside the Wasm module and returns the sum of all step counts.  This avoided measuring one process start per Collatz sequence.  These timing notes predate the generic compiler path and should be rerun before serving as current benchmark evidence.

Superseded commands run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm collatz-emit --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 27 --iters 10000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 27 10000000`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 63728127 --iters 1000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 63728127 1000000`
- [x] `.lake/build/bin/lean-wasm collatz-bench --input 989345275647 --iters 1000000`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke collatz_bench build/collatz.wasm 989345275647 1000000`

## 2026-05-06: Generic UInt64 Compiler Fragment

`LeanExe.IR.Core` is now the generic executable IR for the first compiler fragment.  `LeanExe.Extract.Core` loads checked declarations from a Lean environment, collects supported project-local function dependencies, extracts the accepted `UInt64` and bounded-`Nat` fragment, and emits through `LeanExe.Wasm.Binary.CoreWasm`.  Collatz now compiles through `lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wasm`; there is no `LeanExe.Extract.Collatz` compiler path.

The first fragment supports monomorphic first-order functions returning `UInt64`, `UInt64` and bounded `Nat` parameters represented as Wasm `i64`, numeric literals, primitive `UInt64` arithmetic, `if`, boolean equality, boolean conjunction and disjunction, direct calls, and tail recursion over a decreasing `Nat` fuel argument.  Unsupported code fails during extraction with a reason.  Source-to-IR correctness remains unproved.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.steps --out build/collatz.wat`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Collatz --entry LeanExe.Examples.Collatz.bench --out build/collatz-bench.wasm`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke steps build/collatz.wasm 27`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke steps build/collatz.wasm 989345275647`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke bench build/collatz-bench.wasm 27 10`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke bench build/collatz-bench.wasm 989345275647 3`
- [x] `lake build LeanExe.Examples.Arithmetic`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Arithmetic --entry LeanExe.Examples.Arithmetic.affine --out build/affine.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Arithmetic --entry LeanExe.Examples.Arithmetic.choose --out build/choose.wasm`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke affine build/affine.wasm 5 11`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke choose build/choose.wasm 0 41`
- [x] `env XDG_CACHE_HOME=/tmp /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime run --invoke choose build/choose.wasm 8 41`
- [x] `node test/fuzz_validate.js build/validate.wasm 200`
