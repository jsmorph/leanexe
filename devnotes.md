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
| Wasmtime release artifacts | https://github.com/bytecodealliance/wasmtime/releases |

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

Limitation at that checkpoint: the generic compiler fragment supported only monomorphic first-order functions returning `UInt64`, `UInt64` and bounded `Nat` parameters represented as Wasm `i64`, primitive arithmetic, direct calls, `if`, boolean equality and disjunction, and tail recursion over a decreasing `Nat` fuel argument.  It did not lower arbitrary Lean expressions, data structures, pattern matching over user inductives, arrays, byte arrays, typeclasses beyond the primitive patterns it recognized, or IO.  `compile-wat` printed WAT from the same IR used by binary emission.  The verification pass compared Lean and Wasmtime for `27`, `989345275647`, `bench 27 10`, and `bench 989345275647 3`.

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

At this checkpoint, the first fragment supported monomorphic first-order functions returning `UInt64`, `UInt64` and bounded `Nat` parameters represented as Wasm `i64`, numeric literals, primitive `UInt64` arithmetic, `if`, boolean equality, boolean conjunction and disjunction, direct calls, and tail recursion over a decreasing `Nat` fuel argument.  Unsupported code failed during extraction with a reason.  Source-to-IR correctness remained unproved.

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

## 2026-05-06: Naive Integer Map

`LeanExe.Examples.IntMap` is a simple open-addressed table from `UInt64` keys to `UInt64` values.  It uses 256 slots, stores each slot as adjacent key and value cells in an `Array UInt64`, reserves key `0` as empty, inserts keys `1` through `100`, maps key `k` to `k * 10 + 7`, and exports `query` and `checksum`.  `checksum` sums all 100 mapped values and returns `51200`.

The example required generic array support in the checked-declaration compiler.  At this checkpoint, the IR had `Array UInt64` pointer values, zero-filled allocation, indexed loads, and indexed stores.  The extractor recognized `Array.replicate n 0`, `Array.get!Internal`, `Array.set!`, boolean-valued helper functions represented as `0` or `1`, and zero-argument project declarations used as constants.  It rejected nonzero `Array.replicate` fills, because the Wasm lowering did not initialize arbitrary values.

That initial array lowering mutated Wasm memory in place and assumed linear use of arrays across updates.  That matched the integer-map example, but it did not implement Lean array alias semantics.  The later copy-on-write array section supersedes this lowering.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.IntMap --entry LeanExe.Examples.IntMap.query --out .lake/build/intmap-query.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.IntMap --entry LeanExe.Examples.IntMap.query --out .lake/build/intmap-query.wat`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.IntMap --entry LeanExe.Examples.IntMap.checksum --out .lake/build/intmap-checksum.wasm`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke query .lake/build/intmap-query.wasm 1` returned `17`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke query .lake/build/intmap-query.wasm 100` returned `1007`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke query .lake/build/intmap-query.wasm 101` returned `0`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke checksum .lake/build/intmap-checksum.wasm` returned `51200`.
- [x] `lake env lean --stdin` with `#eval LeanExe.Examples.IntMap.query 1`, `#eval LeanExe.Examples.IntMap.query 100`, `#eval LeanExe.Examples.IntMap.query 101`, and `#eval LeanExe.Examples.IntMap.checksum` returned `17`, `1007`, `0`, and `51200`.

## 2026-05-06: Next Prime

`LeanExe.Examples.Prime.next : UInt64 -> UInt64` returns the first prime greater than the input within a fixed search fuel of `100000` candidate values.  It uses a naive divisor scan from `2` to `n - 1`, represented as decreasing `Nat`-fuel recursion, and returns `0` if the candidate search fuel is exhausted.  This example exercises the scalar compiler path without adding new primitives.

Checks run:

- [x] `lake build LeanExe.Examples.Prime`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Prime --entry LeanExe.Examples.Prime.next --out .lake/build/prime-next.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Prime --entry LeanExe.Examples.Prime.next --out .lake/build/prime-next.wat`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 0` returned `2`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 2` returned `3`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 14` returned `17`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke next .lake/build/prime-next.wasm 1000` returned `1009`.
- [x] `lake env lean --stdin` with the same four `#eval LeanExe.Examples.Prime.next` calls returned `2`, `3`, `17`, and `1009`.

## 2026-05-06: Correct Array UInt64 Semantics

The CoreWasm array layout now stores `Array UInt64` values as pointers to a length header followed by eight-byte cells.  `Array.replicate n 0` writes the length and allocates zero-filled cells.  `Array.get!Internal` and `GetElem?.getElem!` check the index before loading; an out-of-bounds index emits a Wasm trap, matching ordinary Lean execution of `a[i]!`.  `Array.set!` evaluates its arguments, checks the index, allocates a fresh array, copies all cells, updates one cell, and returns the new pointer.  Old aliases keep pointing at the old array.

`LeanExe.Examples.ArraySemantics.aliasCheck` captures the aliasing case that the old in-place lowering got wrong.  The program builds a base array with element `0` equal to `11`, computes `(a.set! 0 22)[0]! * 100 + a[0]!`, and returns `2211`.  The old in-place lowering would have returned `2222`.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ArraySemantics --entry LeanExe.Examples.ArraySemantics.aliasCheck --out .lake/build/array-alias.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ArraySemantics --entry LeanExe.Examples.ArraySemantics.oobGet --out .lake/build/array-oob-get.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ArraySemantics --entry LeanExe.Examples.ArraySemantics.oobSet --out .lake/build/array-oob-set.wasm`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke aliasCheck .lake/build/array-alias.wasm` returned `2211`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke oobGet .lake/build/array-oob-get.wasm` trapped with `wasm unreachable`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke oobSet .lake/build/array-oob-set.wasm` trapped with `wasm unreachable`.
- [x] `lake env lean --stdin` with `#eval LeanExe.Examples.ArraySemantics.aliasCheck` returned `2211`.
- [x] The integer-map regression still returned `17`, `1007`, `0`, and `51200` for `query 1`, `query 100`, `query 101`, and `checksum`.

## 2026-05-06: Local Let Bindings

The generic extractor now lowers Lean `.letE` expressions into `LeanExe.IR.Expr.letE` with an explicit local slot.  The slot allocator threads through nested expressions, branches, conditions, call arguments, and the supported `Nat.brecOn` tail-recursion shape.  Recursive update temporaries now start after locals required by extracted loop conditions and recursive arguments, preventing collisions between let-bound locals and loop-update staging slots.

The CoreWasm emitter lowers an IR let by evaluating the bound value, assigning it to the chosen Wasm local, and emitting the body.  At that checkpoint, the implementation accepted let-bound `Bool`, `UInt64`, bounded `Nat`, and `Array UInt64` values.  Product lets were added later.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Let`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.aliasLet --out .lake/build/let-alias.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.singleArrayUse --out .lake/build/let-single-array.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.boolLet --out .lake/build/let-bool.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.letCondition --out .lake/build/let-condition.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.recArgLetDemo --out .lake/build/let-rec-arg.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.branchArray --out .lake/build/let-branch-array.wasm`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.bumpDemo --out .lake/build/let-bump-demo.wasm`
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke aliasLet .lake/build/let-alias.wasm` returned `2211`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke singleArrayUse .lake/build/let-single-array.wasm` returned `14`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke boolLet .lake/build/let-bool.wasm 3` returned `44`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke boolLet .lake/build/let-bool.wasm 2` returned `55`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke letCondition .lake/build/let-condition.wasm 3` returned `1`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke letCondition .lake/build/let-condition.wasm 2` returned `0`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke recArgLetDemo .lake/build/let-rec-arg.wasm` returned `10`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke branchArray .lake/build/let-branch-array.wasm 0` returned `5`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke branchArray .lake/build/let-branch-array.wasm 1` returned `9`.
- [x] `env XDG_CACHE_HOME=/home/somebody/src/leanexe/.lake/build/cache /tmp/wasmtime-runtime.GEHkKm/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke bumpDemo .lake/build/let-bump-demo.wasm` returned `2`.
- [x] Lean evaluation for `aliasLet`, `singleArrayUse`, `boolLet 3`, `boolLet 2`, `letCondition 3`, `letCondition 2`, `recArgLetDemo`, `branchArray 0`, `branchArray 1`, and `bumpDemo` returned `2211`, `14`, `44`, `55`, `1`, `0`, `10`, `5`, `9`, and `2`.
- [x] At that checkpoint, `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Let --entry LeanExe.Examples.Let.unsupportedLetPair --out .lake/build/let-unsupported-pair.wasm` failed with `unsupported let-bound type: Prod.{0, 0} UInt64 UInt64`.

## 2026-05-06: Core Correctness Corpus

`LeanExe.Examples.Correctness` collects small checked Lean programs that stress semantic edges in the generic compiler fragment.  At that checkpoint, the accepted cases covered boolean short-circuiting with skipped traps, `UInt64` division and remainder at zero divisors, wraparound arithmetic, nested lexical shadowing, lets in call arguments, array update and read ordering, and lets inside recursive arguments.  The rejected cases covered product lets, nonzero array replication, higher-order arguments, and `IO`.

The corpus found three concrete issues.  CoreWasm condition lowering used Wasm `i32.and` and `i32.or`, which evaluated both operands and therefore trapped for `true || rhs` and `false && rhs` when `rhs` contained an out-of-bounds array access.  CoreWasm `UInt64` division and remainder used Wasm `i64.div_u` and `i64.rem_u` directly, but Lean returns `0` for `x / 0` and `x` for `x % 0`.  The signed LEB128 encoder for `i64.const` emitted invalid Wasm for `UInt64` constants above `Int64.max`; those constants now lower through the signed two’s-complement representation of the same 64-bit pattern.

The corpus also exposed a limitation in the first `Nat.brecOn` tail-recursion extractor.  The old lowering assumed that the loop result was the last carried parameter.  The extractor now parses the generated matcher, extracts the base arm, extracts an optional early-exit value from the successor arm, and emits a result expression that distinguishes fuel exhaustion from early exit.  The successor arm still must either tail-call the recursive handle or use `if cond then exitValue else recursiveCall`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] Lean evaluation for `shortOrSkipsTrap`, `shortAndSkipsTrap`, `divByZero`, `modByZero`, `overflow`, `underflow`, `nestedShadow 3`, `callArgLets 7`, `arrayUpdateRead`, `recLetDemo`, and `recExitDemo` returned `1`, `0`, `0`, `5`, `0`, `18446744073709551615`, `64`, `809`, `110`, `518`, and `314`.
- [x] `node test/core_correctness.js` returned `checked 11 accepted and 4 rejected cases`.
- [x] `node test/fuzz_validate.js .lake/build/validate.wasm 200` returned `checked 206 cases`.
- [x] Wasmtime regressions returned `2211` for array aliasing, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `111` for `Collatz.steps 27`.

## 2026-05-06: Internal Product Values

The extractor now represents products as structured extractor values rather than Wasm values.  Product construction, `.1`, `.2`, product-valued local lets, product-valued `if` expressions, nested products, products containing `Array UInt64` pointers, and projections inside recursive-call arguments compile when every field belongs to the first fragment.  Product-valued entry parameters and product-valued entry results remain rejected, because the CoreWasm ABI still exports scalar `i64` values and array pointers only.

Product projection follows Lean’s lazy projection behavior.  `(bad, value).2` and `let pair := (bad, value); pair.2` do not evaluate `bad`, so the extractor keeps products as field expressions and selects the demanded field.  The same work fixed unused scalar lets: `let x := bad; value` no longer forces `bad` when `x` is not referenced by the body.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] Lean evaluation for `productLet`, `nestedProduct`, `productSkipsUnusedField`, `productBranch 0`, `productBranch 1`, `productArrayAlias`, `recProductDemo`, and `unusedScalarLetSkipsTrap` returned `12`, `203`, `7`, `12`, `34`, `2211`, `10`, and `1`.
- [x] `node test/core_correctness.js` returned `checked 19 accepted and 5 rejected cases`.
- [x] `node test/fuzz_validate.js .lake/build/validate.wasm 200` returned `checked 206 cases`.
- [x] Node WebAssembly smoke regressions returned `2211` for array aliasing, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `111` for `Collatz.steps 27`.

## 2026-05-06: Lazy Bindings, Option Values, and Strict Calls

The next correctness pass found a mismatch between Lean evaluation and the eager scalar-let lowering.  Lean returns `7` for `let x := bad; (x, 7).2`, because the projection does not demand the first product field.  The extractor now represents let-bound values as thunks over the checked expression and its de Bruijn environment, forcing the thunk only when the body demands it.

The same issue applies to nonrecursive helper calls.  Lean returns `1` for `ignore bad` when the helper ignores its argument, while Wasm function calls evaluate arguments before entering the callee.  The extractor now inlines nonrecursive project-local helper calls with lazy argument thunks; recursive helpers still compile as Wasm functions when the supported `Nat.brecOn` loop extraction requires that representation.

The extractor now computes demand summaries for project-local helper calls.  Each summary records parameters that may be demanded and parameters that must be demanded when the helper result is demanded.  Strict Wasm calls are rejected when an argument may trap and the callee does not must-demand the corresponding parameter.  `LeanExe.Examples.Correctness.rejectRecursiveIgnoredTrapArg` captures the direct case: Lean evaluates the program to `7`, while the old Wasm lowering trapped before the helper could take its fuel-zero base branch.  `rejectRecursiveIgnoredHiddenTrapArg` captures the indirect case, where the trap is hidden behind a zero-argument project-local declaration.  Recursive summaries are conservative: the fuel parameter is must-demanded, carried parameters are may-demanded, and a later pass should either inline supported loop calls at the call site or compute more precise carried-parameter demand.

`Option` values are now extractor-level tagged values.  `Option.none`, `Option.some`, local `Option` lets, `if` expressions returning `Option`, and matches over `Option UInt64` compile when the final entry result remains a scalar first-fragment value.  `Option` entry parameters and entry results remain rejected because the current Wasm ABI exposes only scalar `i64` values and array pointers.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 29 accepted and 9 rejected cases`.
- [x] Lean evaluation for `letUsedOnlyInUnusedProductField`, `ignoredCallArgSkipsTrap`, `callArgUsedOnlyInUnusedProductField`, `optionSomeMatch`, `optionNoneMatchSkipsSomeArm`, `optionSomeMatchSkipsUnusedPayload`, `optionLet`, `optionBranch 0`, and `optionBranch 1` returned `7`, `1`, `7`, `8`, `5`, `9`, `18`, `11`, and `34`.
- [x] Lean evaluation for `recursiveDemandedFuelGet`, `rejectRecursiveIgnoredTrapArg`, and `rejectRecursiveIgnoredHiddenTrapArg` returned `7`, `7`, and `7`; compilation accepts the demanded-fuel case and rejects the ignored-argument cases.
- [x] `node test/fuzz_validate.js .lake/build/validate.wasm 200` returned `checked 206 cases`.
- [x] Wasmtime 44.0.0 from `build/tools/wasmtime/current/wasmtime` returned `11` and `34` for `optionBranch 0` and `optionBranch 1`.
- [x] Wasmtime regressions returned `111` for `Collatz.steps 27`, `51200` for `IntMap.checksum`, `1009` for `Prime.next 1000`, and `2211` for array aliasing.

## 2026-05-06: Generic Read-Only ByteArray Input

The generic compiler now accepts a `ByteArray` parameter as a structured extractor value backed by two Wasm ABI slots: pointer and length.  `ByteArray.size` reads the length slot, and `ByteArray.get!` lowers to a bounds check followed by `i32.load8_u` and zero extension to the scalar `i64` representation.  Function calls and the supported `Nat.brecOn` loop shape flatten `ByteArray` values when crossing a strict Wasm call boundary, while Lean source functions still see one `ByteArray` parameter.

`LeanExe.Examples.AsciiDigits.validateGeneric : ByteArray -> Bool` is the first byte-buffer program compiled through `lean-wasm compile`.  It keeps the original proof-oriented `validate` declaration unchanged and uses a fuel-bounded loop over the input length plus one, so the empty input returns `true` and the terminal length check does not read past the end of the buffer.  The generic validator is still read-only: the host writes bytes into exported memory and calls the entry function as `validateGeneric(ptr, len)`.

Wasmtime was no longer present under `/tmp`, so this pass downloaded the official Wasmtime 36.0.9 `aarch64-linux` release into `.lake/build/tools`.  That release is marked latest on the upstream GitHub releases page as of 2026-05-06.  The Wasmtime check uses a generated WAST file with active data segments because the generic module exports memory but does not yet export `alloc` or a host helper for writing byte inputs through the CLI.

Checks run:

- [x] `lake build`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wat`
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 200` returned `checked 206 cases`.
- [x] `.lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --version` returned `wasmtime 36.0.9 (c59270b18 2026-05-05)`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/ascii-generic.wast` accepted generated assertions for empty input, all-digit input, invalid input, and a valid prefix.

## 2026-05-06: Generic Comparison Primitives

The generic IR now has unsigned `<` and `<=` conditions.  The extractor recognizes Lean conditions elaborated as `LT.lt` and `LE.le`, including conditions over bounded `Nat` and `UInt64` values, and CoreWasm lowers them to `i64.lt_u` and `i64.le_u`.  This keeps the current fixed-width representation explicit: accepted runtime `Nat` comparisons are comparisons over the bounded `i64` values already admitted into the fragment, not arbitrary-precision `Nat` execution.

`LeanExe.Examples.AsciiDigits.isAsciiDigitNat` now uses the source-level range check `48 <= n` and `n <= 57` instead of ten equality tests.  `LeanExe.Examples.Correctness` adds separate `Nat` and `UInt64` comparison cases for values below, at, and above the branch boundary.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 35 accepted and 9 rejected cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wat`
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 200` returned `checked 206 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/ascii-generic.wast` accepted generated assertions for empty input, all-digit input, invalid input, and a valid prefix.

## 2026-05-06: Generic Array Size

The generic IR now has `Array.size` as a scalar expression.  CoreWasm lowers it to an `i64.load` from the array header, the same header already used by bounds checks and copy-on-write updates.  This lets source programs inspect array lengths without adding a new layout rule.

`LeanExe.Examples.Correctness.arraySizeAfterSet` checks that `Array.set!` preserves the length header while returning a fresh array pointer.  The function returns `Nat`, which remains represented as an `i64` in the bounded fragment.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 36 accepted and 9 rejected cases`.

## 2026-05-06: Generic Array Push

The generic compiler now lowers `Array.push` for `Array UInt64`.  CoreWasm evaluates the source array and pushed value, loads the old length, allocates a new array with length `oldLen + 1`, copies existing cells, writes the pushed value at the old length, and returns the new pointer.  This matches the conservative copy-on-write discipline already used by `Array.set!`, so old aliases keep the old length and old cells.

`LeanExe.Examples.Correctness.arrayPushRead` checks the pushed length, old-array length, preserved first cell, and new last cell.  The direct Wasmtime check exercises the emitted binary for that example rather than only Node’s WebAssembly runtime.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 37 accepted and 9 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayPushRead .lake/build/core-correctness/arrayPushRead.wasm` returned `507`.

## 2026-05-06: Generic Allocator Exports

Generic CoreWasm modules now export `alloc(len : i64) -> i64` and `reset()`.  The heap global starts at byte offset `4096`, matching the original validator module, and every generic array allocation uses the same heap global.  A host that needs to pass a `ByteArray` can now call `reset`, call `alloc`, write bytes at the returned pointer, and pass `(ptr, len)` to the entry function without guessing a memory address that might overlap later compiled allocations.

The generic function indices remain stable because the runtime functions are appended after user functions.  User calls still refer to the same indices, and the runtime exports use indices `funcs.size` and `funcs.size + 1`.  The validator fuzz harness now uses the generic allocator when `validateGeneric`, `alloc`, and `reset` are present, while retaining support for the older hand-written validator ABI.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 37 accepted and 9 rejected cases`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wasm`
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.AsciiDigits --entry LeanExe.Examples.AsciiDigits.validateGeneric --out .lake/build/ascii-generic.wat`
- [x] `node test/fuzz_validate.js .lake/build/ascii-generic.wasm 200` returned `checked 206 cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke alloc .lake/build/ascii-generic.wasm 4` returned `4096`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/ascii-generic.wast` accepted allocator and validator assertions.

## 2026-05-06: Nonzero Array Replication

`Array.replicate` now supports nonzero `UInt64` fill values.  CoreWasm still uses the zero-allocation path for literal zero fills, but nonzero fills evaluate the length and value, allocate the array header and cells, and run a fill loop that writes the value into each cell.  The value is evaluated once before the fill loop, matching the source-level call argument.

`LeanExe.Examples.Correctness.nonzeroReplicateRead` checks the new path by reading two initialized cells and checking the resulting size.  The previous rejection case for nonzero replication was removed from the correctness harness because the feature now compiles.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 38 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke nonzeroReplicateRead .lake/build/core-correctness/nonzeroReplicateRead.wasm` returned `77`.

## 2026-05-06: Generic Array Pop

The generic compiler now lowers `Array.pop` for `Array UInt64`.  Empty arrays return the original pointer, matching Lean’s empty-pop behavior.  Nonempty arrays allocate a fresh array with length `oldLen - 1`, copy the retained prefix, and return the new pointer, preserving the copy-on-write rule used by `set!` and `push`.

`LeanExe.Examples.Correctness.arrayPopRead` checks pop after push, the old array length, the popped array length, empty-pop behavior, and retained cells.  The Wasmtime check runs the emitted binary for that example.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 39 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayPopRead .lake/build/core-correctness/arrayPopRead.wasm` returned `44`.

## 2026-05-06: UInt64 Bitwise Or and Xor

The scalar IR now supports `UInt64.lor` and `UInt64.xor`, complementing the existing `UInt64.land` lowering.  CoreWasm emits `i64.or` and `i64.xor`; these operations preserve the current fixed-width `UInt64` representation without adding new ABI rules.

`LeanExe.Examples.Correctness.bitwiseOrXor` checks the new operations together with `land`, and Wasmtime runs the emitted binary for that case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 40 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke bitwiseOrXor .lake/build/core-correctness/bitwiseOrXor.wasm` returned `6`.

## 2026-05-06: UInt64 Shifts

The scalar IR now supports `UInt64.shiftLeft` and `UInt64.shiftRight`.  Local Lean checks showed that Lean masks the shift count modulo 64 for `UInt64`, matching Wasm `i64.shl` and `i64.shr_u`; for example, shifting by `65` behaves like shifting by `1`.

`LeanExe.Examples.Correctness.shiftMasking` checks both left and right shifts with a count of `65`, and Wasmtime runs the emitted binary for that case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 41 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke shiftMasking .lake/build/core-correctness/shiftMasking.wasm` returned `42`.

## 2026-05-06: Greater-Than Comparisons

The extractor now recognizes Lean conditions elaborated as `GT.gt` and `GE.ge`.  They lower by reversing the operands of the existing unsigned `<` and `<=` IR conditions, so no new Wasm condition form was needed.

`LeanExe.Examples.Correctness.greaterComparisons` checks `>` and `>=` across the below, boundary, and above cases.  Wasmtime runs the emitted binary for the above case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 44 accepted and 8 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke greaterComparisons .lake/build/core-correctness/greaterComparisons.wasm 6` returned `30`.

## 2026-05-06: Reserved Runtime Export Names

Generic modules now reject entry points whose short export name would collide with runtime exports.  The reserved names are `memory`, `alloc`, and `reset`.  Without this check, a source function named `alloc` could compile to a module with duplicate exports after the generic allocator was added.

`LeanExe.Examples.Correctness.alloc` is a valid scalar Lean definition, but compiling it as an entry now fails with `entry export name is reserved by the runtime ABI: alloc`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 44 accepted and 9 rejected cases`.

## 2026-05-06: ByteArray Input with Later Allocation

`LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray` exercises a mixed ByteArray-and-array program.  The host passes a `ByteArray` through the generic `(ptr, len)` ABI, and the compiled function then allocates an `Array UInt64` before reading the input byte.  This catches heap-overlap regressions in the generic allocator: input allocated by the host must remain valid after compiled code allocates.

`test/bytearray_alloc.js` builds the example module, compiles it through `lean-wasm compile`, allocates host input through the module’s exported allocator, writes the bytes into memory, and calls the compiled entry.  The Wasmtime WAST check covers the same scenario with an active data segment at the allocator’s first returned pointer.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray --out .lake/build/bytearray-first-plus-array.wasm`
- [x] `node test/bytearray_alloc.js` returned `checked 3 bytearray allocation cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.ByteArrayPrograms --entry LeanExe.Examples.ByteArrayPrograms.firstBytePlusArray --out .lake/build/bytearray-first-plus-array.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime wast .lake/build/bytearray-first-plus-array.wast` accepted the allocator-plus-entry assertion.

## 2026-05-06: Nat Subtraction Semantics

The extractor previously lowered every `HSub.hSub` application to wrapping `i64.sub`.  That was correct for `UInt64`, but wrong for `Nat`: Lean’s `Nat` subtraction saturates at zero.  The extractor now inspects the primitive result type and emits a dedicated bounded-`Nat` subtraction operation for `Nat` results.  CoreWasm evaluates both operands once, returns `0` when `left < right`, and otherwise emits `left - right`.

`LeanExe.Examples.Correctness.natSubSaturates` checks the underflow case, and `natSubNormal` checks ordinary subtraction.  `UInt64` subtraction still uses wrapping subtraction, so the existing `underflow` test continues to return `18446744073709551615`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 46 accepted and 9 rejected cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke natSubSaturates .lake/build/core-correctness/natSubSaturates.wasm` returned `0`.

## 2026-05-06: Bounded Nat Literal Rejection

Runtime `Nat` literals now receive an explicit bound check during extraction.  Literals below `2^64` continue to lower to the scalar `i64` representation; larger literals are rejected with `Nat literal exceeds bounded runtime representation`.  This avoids silently compiling an arbitrary-precision Lean `Nat` literal to its low 64 bits.

`LeanExe.Examples.Correctness.rejectHugeNatLiteral` covers the first out-of-range value, `18446744073709551616`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 46 accepted and 10 rejected cases`.

## 2026-05-06: Checked Nat Addition and Multiplication

The extractor now emits distinct IR operations for `Nat` addition and multiplication instead of reusing wrapping `UInt64` operations.  `Nat` addition evaluates both operands once, computes the `i64` sum, and traps if the unsigned result wrapped below the left operand.  `Nat` multiplication traps when `left > UInt64.max / right`, with a separate zero case.  These traps mark values outside the current bounded `Nat` subset rather than returning a truncated result.

The correctness harness now has a third category for programs that compile but must trap at runtime.  `natAddOverflow` and `natMulOverflow` cover the first overflowing values.  Normal `Nat` addition and multiplication still compile and return their expected bounded results.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 48 accepted, 10 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke natAddOverflow .lake/build/core-correctness/natAddOverflow.wasm` trapped with `wasm unreachable`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke natMulOverflow .lake/build/core-correctness/natMulOverflow.wasm` trapped with `wasm unreachable`.

## 2026-05-06: UInt64.ofNat

The extractor now recognizes `UInt64.ofNat`.  For a literal argument, it lowers directly to a `UInt64` constant, preserving Lean’s modulo-`2^64` behavior for large literals.  For a runtime `Nat` expression, it lowers the bounded scalar value directly; values outside the bounded `Nat` representation cannot arise without a prior trap.

`LeanExe.Examples.Correctness.uint64OfNatValue` checks a runtime bounded conversion, and `uint64OfHugeNat` checks that a literal equal to `2^64` converts to `0` rather than receiving the bounded-`Nat` literal rejection.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 50 accepted, 10 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint64OfHugeNat .lake/build/core-correctness/uint64OfHugeNat.wasm` returned `0`.

## 2026-05-06: ByteArray Result Rejection

The function type checker now distinguishes parameter ABI support from result ABI support.  A `ByteArray` parameter is allowed and flattens to `(ptr, len)`, but a `ByteArray` result is rejected because generic CoreWasm functions still return one `i64`.  This moves byte-array result rejection to the function type boundary instead of letting extraction fail later when a structured value is used as a scalar.

`LeanExe.Examples.Correctness.rejectByteArrayReturn` covers the case.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 50 accepted, 11 rejected, and 2 trapped cases`.

## 2026-05-06: Internal UInt8 Values

`ByteArray.get!` returns `UInt8`, so byte-oriented programs need to compare byte reads with `UInt8` literals without converting through `Nat`.  The extractor now admits `UInt8` as a local scalar type while keeping `UInt8` out of the exported function ABI.  `OfNat UInt8` and `UInt8.ofNat` lower modulo `256`, matching Lean evaluation for values such as `(300 : UInt8).toNat = 44`.

`LeanExe.Examples.ByteArrayPrograms.firstByteIsStar` checks a `ByteArray.get!` result against `(42 : UInt8)`.  `LeanExe.Examples.Correctness.wrappedUInt8Literal` covers literal wrapping, and `uint8OfNatValue` covers runtime bounded-`Nat` conversion through `UInt8.ofNat`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 52 accepted, 11 rejected, and 2 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 6 bytearray allocation cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke wrappedUInt8Literal .lake/build/core-correctness/wrappedUInt8Literal.wasm` returned `44`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint8OfNatValue .lake/build/core-correctness/uint8OfNatValue.wasm 298` returned `43`.

## 2026-05-06: Internal UInt8 Helper Signatures

The compiler now separates exported entry ABI support from project-local helper support.  Exported entries still reject `UInt8` parameters and results, because the public ABI has not assigned byte-sized scalar slots.  Internal helpers may use `UInt8` parameters and results, and the lowering represents those values as scalar `i64` slots constrained by the operations that produce them.

`LeanExe.Examples.ByteArrayPrograms.nextByte` takes and returns `UInt8`.  `firstByteNextIsZero` calls it on a `ByteArray.get!` result and checks the modulo-256 wrap from `255` to `0`.  `LeanExe.Examples.Correctness.rejectUInt8Param` and `rejectUInt8Return` keep the entry boundary explicit.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 52 accepted, 13 rejected, and 2 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 9 bytearray allocation cases`.

## 2026-05-06: UInt8 Arithmetic Wrapping

Accepting internal `UInt8` values made the previous generic lowering of `HAdd`, `HSub`, and `HMul` too broad.  Those primitives reused the `UInt64` operations unless the result type was `Nat`, which would compile `(255 : UInt8) + 1` as `256` instead of `0`.  The extractor now inspects the primitive result type and masks `UInt8` addition, subtraction, and multiplication to eight bits.

`UInt8` division and remainder already match Lean under the existing checked unsigned lowering for zero divisors: `x / 0` returns `0`, and `x % 0` returns `x`.  `LeanExe.Examples.Correctness.uint8AddWrap`, `uint8SubWrap`, `uint8MulWrap`, and `uint8DivModZero` cover these cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 56 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint8AddWrap .lake/build/core-correctness/uint8AddWrap.wasm` returned `0`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke uint8SubWrap .lake/build/core-correctness/uint8SubWrap.wasm` returned `255`.

## 2026-05-06: Bool Pattern Matching

The generic extractor now lowers `Bool.casesOn` and generated `match_*` declarations whose scrutinee type is `Bool`.  Earlier matcher recognition treated every generated matcher as an `Option` matcher, which caused Bool matches to fail while trying to read scalar values as `Option` tags.  The extractor now classifies generated matchers by the scrutinee type in the checked matcher declaration before choosing the Bool or Option lowering.

Bool matches use the existing conditional IR and preserve branch laziness, so a skipped match arm may contain a partial expression such as an out-of-bounds array access.  Structured match results use the same extractor-level `valueIte` path as structured `if` expressions.

`LeanExe.Examples.Correctness.boolMatchScalar`, `boolMatchSkipsTrap`, `boolMatchCondition`, and `boolMatchProduct` cover scalar results, branch laziness, boolean-valued matches used as conditions, and product-valued match results.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 63 accepted, 13 rejected, and 2 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 9 bytearray allocation cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke boolMatchSkipsTrap .lake/build/core-correctness/boolMatchSkipsTrap.wasm` returned `7`.

## 2026-05-06: Decidable Comparison Booleans

Lean programs often use `decide` to turn a decidable proposition into a `Bool`.  The extractor now recognizes `Decidable.decide` when the proposition is already in the supported condition fragment, such as bounded `Nat` or `UInt64` comparisons.  Unsupported propositions still fail through the existing condition extractor rather than receiving a broad or guessed lowering.

`LeanExe.Examples.Correctness.decideNatLt` covers a `Nat` comparison used as an `if` condition through `decide`, and `decideUInt64Ge` covers a `Bool` result produced directly from a decided `UInt64` comparison.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 67 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke decideUInt64Ge .lake/build/core-correctness/decideUInt64Ge.wasm 3` returned `1`.

## 2026-05-06: Scalar Propositional Equality

The condition extractor now supports `Eq` propositions over admitted scalar runtime types: `Bool`, `UInt8`, `UInt64`, and bounded `Nat`.  This admits ordinary Lean forms such as `if x = 3 then ...` and `decide (x = 3)` without requiring source code to use `==`.  Equality over structured values remains unsupported until those values have an explicit equality lowering.

`LeanExe.Examples.Correctness.propEqNat` covers direct propositional equality in an `if`, `decideEqUInt64` covers equality through `Decidable.decide`, and `propEqBoolSkipsTrap` checks that equality against `true` still preserves short-circuit evaluation inside the boolean expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 72 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke propEqBoolSkipsTrap .lake/build/core-correctness/propEqBoolSkipsTrap.wasm` returned `1`.

## 2026-05-06: Proposition Connectives

The condition extractor now supports proposition-level `And`, `Or`, `Not`, `True`, and `False` when their subconditions are already in the supported fragment.  This admits source forms such as `if x > 1 ∧ x < 5 then ...` and `decide (x < 2 ∨ x > 5)`.  The lowering uses the same short-circuiting condition IR as boolean `&&` and `||`.

`LeanExe.Examples.Correctness.propAndNat`, `propOrNat`, and `propNotNat` cover compound `Nat` propositions.  `propOrSkipsTrap` and `propAndSkipsTrap` check that proposition connectives do not evaluate skipped branches containing partial array reads.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 81 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke propOrSkipsTrap .lake/build/core-correctness/propOrSkipsTrap.wasm` returned `1`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke propAndSkipsTrap .lake/build/core-correctness/propAndSkipsTrap.wasm` returned `0`.

## 2026-05-06: Scalar Min and Max

The extractor now lowers `Min.min` and `Max.max` for bounded `Nat`, `UInt8`, and `UInt64`.  The lowering uses unsigned scalar comparisons over the existing runtime representation.  This keeps `Nat.min` and `Nat.max` inside the bounded fragment and gives byte and word-sized code the usual scalar selection operations.

`LeanExe.Examples.Correctness.natMinMax`, `u64MinMax`, and `u8MinMax` cover the supported types.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 86 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke u8MinMax .lake/build/core-correctness/u8MinMax.wasm` returned `280`.

## 2026-05-06: Bitwise Operator Notation

The extractor now lowers `HAnd.hAnd`, `HOr.hOr`, and `HXor.hXor` for `UInt64` and internal `UInt8` values.  Lean elaborates the `&&&`, `|||`, and `^^^` notations through those typeclass operations, while earlier examples used the direct `UInt64.land`, `UInt64.lor`, and `UInt64.xor` functions.

`LeanExe.Examples.Correctness.bitwiseNotation` covers the notation path and returns the same result as the direct-call `bitwiseOrXor` example.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 87 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke bitwiseNotation .lake/build/core-correctness/bitwiseNotation.wasm` returned `6`.

## 2026-05-06: Shift Operator Notation

The extractor now lowers `HShiftLeft.hShiftLeft` and `HShiftRight.hShiftRight` for `UInt64`.  Lean elaborates `<<<` and `>>>` through those typeclass operations, while existing coverage used direct `UInt64.shiftLeft` and `UInt64.shiftRight` calls.

`LeanExe.Examples.Correctness.shiftNotation` covers the notation path and keeps the existing shift-count masking expectation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 88 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke shiftNotation .lake/build/core-correctness/shiftNotation.wasm` returned `42`.

## 2026-05-06: Bitwise Complement

The extractor now lowers `Complement.complement` for `UInt64` and internal `UInt8` values.  `UInt64` complement lowers to xor with `2^64 - 1`; `UInt8` complement lowers to xor with `255`.  The primitive application code also now isolates inline calls, emitted calls, unary primitives, and binary primitives in separate helper functions, which keeps additional primitive cases out of the main expression matcher.

`LeanExe.Examples.Correctness.complementNotation` covers `~~~` on `UInt64`, and `u8Complement` covers the internal `UInt8` path.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 90 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke complementNotation .lake/build/core-correctness/complementNotation.wasm` returned `255`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke u8Complement .lake/build/core-correctness/u8Complement.wasm` returned `255`.

## 2026-05-06: Byte UInt8 Bitwise Coverage

`firstByteLowNibble` exercises `UInt8` bitwise notation on a value returned by `ByteArray.get!`.  This covers the path real byte-oriented code uses: host input enters memory, `ByteArray.get!` produces an internal `UInt8`, and `&&&` lowers through `HAnd.hAnd` without converting through `Nat`.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 12 bytearray allocation cases`.

## 2026-05-06: ByteArray.isEmpty

The extractor now lowers `ByteArray.isEmpty` to a length comparison against zero.  This is the same value already available through the `ByteArray` parameter ABI, so it adds a source-level convenience without changing the memory representation.

`LeanExe.Examples.ByteArrayPrograms.emptyViaIsEmpty` covers the new primitive in the byte-array allocation harness.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 14 bytearray allocation cases`.

## 2026-05-06: ByteArray Bang Indexing

`input[i]!` for `ByteArray` elaborates through `GetElem?.getElem!`, not `ByteArray.get!`.  The extractor now distinguishes the receiver type for `GetElem?.getElem!` and lowers `ByteArray` receivers to the byte-array bounds check and `i32.load8_u` path.  `Array UInt64` receivers continue to use the existing array load path.

`LeanExe.Examples.ByteArrayPrograms.firstByteBangIndex` covers empty input and two byte values through the byte-array allocation harness.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 17 bytearray allocation cases`.
- [x] `node test/core_correctness.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`.

## 2026-05-06: Mixed ByteArray and Scalar ABI

`LeanExe.Examples.ByteArrayPrograms.byteAtOrZero` takes a `ByteArray` followed by a bounded `Nat` index.  This checks that the flattened byte-array ABI slots `(ptr, len)` compose with later scalar parameters in the exported Wasm signature.  The host calls the compiled function as `(ptr, len, index)`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 20 bytearray allocation cases`.

## 2026-05-06: Array.isEmpty

The extractor now lowers `Array.isEmpty` for `Array UInt64` by reading the array header length and comparing it with zero.  This matches the existing memory layout and avoids requiring source programs to write `a.size == 0`.

`LeanExe.Examples.Correctness.arrayIsEmptyValues` checks both empty and non-empty arrays.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 91 accepted, 13 rejected, and 2 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayIsEmptyValues .lake/build/core-correctness/arrayIsEmptyValues.wasm` returned `1`.

## 2026-05-06: Array.back!

The extractor now lowers `Array.back!` for `Array UInt64`.  It evaluates the array expression once, binds the array pointer in a local, computes `size - 1`, and reuses the existing bounds-checked array load.  Empty arrays therefore trap through the same `unreachable` path as an out-of-bounds indexed read.

`LeanExe.Examples.Correctness.arrayBackRead` covers the non-empty case.  `arrayBackEmptyTrap` compiles but must trap at runtime.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 92 accepted, 13 rejected, and 3 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayBackRead .lake/build/core-correctness/arrayBackRead.wasm` returned `9`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayBackEmptyTrap .lake/build/core-correctness/arrayBackEmptyTrap.wasm` trapped with `wasm unreachable`.

## 2026-05-06: Array.getD

The extractor now lowers `Array.getD` for `Array UInt64`.  It binds the array pointer and index once, checks the index against the header length, and returns either the bounds-checked load or the default expression.  The default expression stays in the else branch, so an in-bounds read does not evaluate a default that would trap.

`LeanExe.Examples.Correctness.arrayGetDRead` covers in-bounds and out-of-bounds reads.  `arrayGetDSkipsDefaultTrap` checks default-branch laziness.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayGetDRead .lake/build/core-correctness/arrayGetDRead.wasm 2` returned `99`.
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayGetDSkipsDefaultTrap .lake/build/core-correctness/arrayGetDSkipsDefaultTrap.wasm` returned `5`.

## 2026-05-06: Combined Correctness Runner

`test/run_all.js` runs the current local correctness suite: `lake build`, `test/core_correctness.js`, `test/bytearray_alloc.js`, and `test/fuzz_validate.js`.  The fuzz case count defaults to `50` and can be changed through `LEANEXE_FUZZ_CASES`.  The runner uses `LEAN_WASM_EXE` when set, matching the existing harnesses.

Checks run:

- [x] `node test/run_all.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`, `checked 14 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Scalar Then ByteArray ABI

`LeanExe.Examples.ByteArrayPrograms.prefixPlusFirstByte` takes a scalar `UInt64` before a `ByteArray`.  This checks the other mixed-parameter order for the flattened byte-array ABI: the exported Wasm function receives `(prefix, ptr, len)`.  The prior byte-array harness covered `(ptr, len, scalar)`, so the test suite now exercises both sides of the source-order rule.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 23 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 95 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt8 Shifts

The extractor now lowers `UInt8` shift notation and the direct `UInt8.shiftLeft` and `UInt8.shiftRight` functions.  Lean’s `UInt8` shift semantics mask the shift count modulo eight.  Left shifts also wrap the result to eight bits.  The lowering implements that rule with an explicit `count &&& 7` expression and the existing `UInt8` result mask.

`LeanExe.Examples.Correctness.uint8ShiftNotation` covers `<<<` and `>>>` notation.  `uint8DirectShift` covers the named functions, including an overflowing left shift and a right shift whose count equals eight.  Both examples return `Nat` values so the current public ABI remains unchanged.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 97 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 97 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array.append

The IR now has an `arrayAppend` expression for `Array UInt64`.  The extractor lowers `Array.append` by evaluating both array arguments once and passing their pointers to that IR expression.  CoreWasm allocates a fresh array, stores the combined length, copies the left cells, and then copies the right cells at an offset equal to the left length.

This implementation follows the same conservative copy-on-write discipline as `Array.set!`, `Array.push`, and nonempty `Array.pop`.  Old aliases keep observing the old arrays.  The WAT printer now has the same append lowering as the binary emitter, and the Wasmtime WAT check covers the generated text path.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 99 accepted, 13 rejected, and 3 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayAppendRead --out .lake/build/core-correctness/arrayAppendRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayAppendRead .lake/build/core-correctness/arrayAppendRead.wat` returned `11223344`.
- [x] `node test/run_all.js` returned `checked 99 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.getD

The extractor now lowers `Option.getD` for first-fragment payloads.  It reuses the existing extractor-level tag and payload representation, returning the default value when the tag is zero and the payload otherwise.  The default expression remains inside the `none` branch of the emitted value, so a default that would trap is skipped when the option is `some`.

`LeanExe.Examples.Correctness.optionGetDNone` covers the `none` branch.  `optionGetDSomeSkipsDefaultTrap` checks default laziness with an empty-array `back!` expression.  `optionGetDProduct` checks that structured product payloads pass through the same lowering before projection.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 102 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 102 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option Tag Tests

The extractor now lowers `Option.isSome` and `Option.isNone`.  Both operations inspect only the extractor-level tag and return a scalar `Bool`.  The payload expression is left unused, so a `some` payload that would trap is not evaluated by a tag test.

`LeanExe.Examples.Correctness.optionIsSomeSkipsPayloadTrap` checks that payload laziness.  `optionIsNoneValues` covers both `none` and `some` values in a boolean condition.  These cases keep `Option` inside the existing internal structured-value representation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 104 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 104 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.elim

The extractor now lowers `Option.elim` for first-fragment result values.  The lowering extracts the option tag and payload, then emits the default arm for `none` and the function arm for `some`.  Both arms remain branch-local in the emitted value, so the default expression is skipped for `some` and the function body is skipped for `none`.

`LeanExe.Examples.Correctness.optionElimSomeSkipsDefaultTrap` checks the skipped-default case.  `optionElimNoneSkipsSomeArmTrap` checks the skipped-function case.  `optionElimProduct` checks a product result, which exercises the structured-value branch path rather than only scalar extraction.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 107 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 107 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.map

The extractor now lowers `Option.map` when the mapping function is a one-argument lambda and the result type remains inside the first fragment.  The result keeps the original option tag.  The mapped payload is emitted only for the `some` branch, while the `none` branch uses the default payload for the mapped result type.

`LeanExe.Examples.Correctness.optionMapSome` covers a scalar mapped value.  `optionMapNoneSkipsFunctionTrap` checks that the mapping function is not evaluated for `none`.  `optionMapProduct` checks a structured product result inside an `Option`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 110 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 110 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option.bind

The extractor now lowers `Option.bind` when the bind function is a one-argument lambda returning a supported `Option` value.  If the input option is `none`, the result tag is `none` and the bind function body is not emitted on the executed path.  If the input option is `some`, the result takes the tag and payload produced by the bind function.

`LeanExe.Examples.Correctness.optionBindSome` covers the ordinary `some` case.  `optionBindNoneSkipsFunctionTrap` checks that the bind function is skipped for `none`.  `optionBindFunctionNone` and `optionBindProduct` cover a function that returns `none` and a function that returns an `Option` carrying a product.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 114 accepted, 13 rejected, and 3 trapped cases`.
- [x] `node test/run_all.js` returned `checked 114 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array.extract

The IR now has an `arrayExtract` expression for `Array UInt64`.  The extractor lowers `Array.extract` by evaluating the array, start index, and stop index once.  CoreWasm clamps stop to the source length, computes a zero result length when the effective stop is not greater than start, allocates a fresh array, and copies the selected cells from `start + i` into result cell `i`.

`LeanExe.Examples.Correctness.arrayExtractRead` covers an ordinary interior slice.  `arrayExtractClamps` covers stop clamping, start past the end, and stop before start.  The WAT path is checked with Wasmtime for the clamping case because this feature adds a new text-emitter branch as well as a binary-emitter branch.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 116 accepted, 13 rejected, and 3 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayExtractClamps --out .lake/build/core-correctness/arrayExtractClamps.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayExtractClamps .lake/build/core-correctness/arrayExtractClamps.wat` returned `340`.
- [x] `node test/run_all.js` returned `checked 116 accepted, 13 rejected, and 3 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat.succ and Nat.pred

The extractor now lowers direct `Nat.succ` and `Nat.pred` applications.  `Nat.succ` uses the existing checked bounded-`Nat` addition operation with an increment of one, so it traps when the result would exceed the current `i64` representation.  `Nat.pred` uses the existing bounded-`Nat` subtraction operation with a decrement of one, so predecessor at zero returns zero.

`LeanExe.Examples.Correctness.natSuccPred` covers normal successor and predecessor behavior at `5` and the predecessor-at-zero case.  `natSuccOverflow` compiles and traps at runtime, matching the bounded-`Nat` overflow policy used by addition.  This change adds source coverage for code that uses the named `Nat` operations instead of arithmetic notation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 118 accepted, 13 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 118 accepted, 13 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Fixed-Width Scalar Conversions

The extractor now lowers `Nat.toUInt64`, `UInt64.toUInt8`, and `UInt8.toUInt64`.  `Nat.toUInt64` follows the same rule as `UInt64.ofNat`: bounded runtime `Nat` values pass through unchanged, and direct literals lower modulo `2^64` instead of going through bounded-`Nat` literal rejection.  `UInt64.toUInt8` masks to eight bits, while `UInt8.toUInt64` preserves the current scalar representation.

`LeanExe.Examples.Correctness.natToUInt64Value` covers a runtime bounded `Nat` conversion, and `natToUInt64Huge` covers the direct large-literal case.  `uint64ToUInt8Wrap` checks byte masking from `300` to `44`.  `uint8ToUInt64Value` checks widening from `UInt8` before `UInt64` arithmetic.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 122 accepted, 13 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 122 accepted, 13 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array Literals

The extractor now lowers `List.toArray` when its argument is a literal `List UInt64`.  This accepts Lean array literal syntax such as `#[]` and `#[10, 20, 30]` without adding general list support.  The lowering allocates an array of the literal length, then uses the existing copy-on-write `arraySet` expression to populate each literal element in source order.

`LeanExe.Examples.Correctness.arrayLiteralRead` covers a nonempty literal.  `arrayEmptyLiteral` covers the empty literal.  The implementation rejects nonliteral lists and non-`UInt64` item types rather than inferring behavior for general `List.toArray`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 124 accepted, 13 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 124 accepted, 13 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Internal UInt32

The extractor now admits `UInt32` as an internal scalar type.  It keeps the public ABI unchanged: exported `UInt32` parameters and results are still rejected.  Local values and helper signatures can use `UInt32`, represented as an `i64` whose producing operations constrain the value to `0..2^32-1`.

The lowering follows Lean’s fixed-width behavior.  `UInt32` literals and `UInt32.ofNat` lower modulo `2^32`, `UInt64.toUInt32` masks to 32 bits, and `UInt32.toNat` and `UInt32.toUInt64` preserve the constrained representation.  Addition, subtraction, multiplication, bitwise operations, complement, shifts, `min`, and `max` now have `UInt32` cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 132 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 132 accepted, 15 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt8 and UInt32 Conversions

The extractor now lowers `UInt8.toUInt32` and `UInt32.toUInt8`.  Widening from `UInt8` to `UInt32` preserves the constrained scalar representation.  Narrowing from `UInt32` to `UInt8` masks to eight bits, matching Lean’s fixed-width conversion behavior.

`LeanExe.Examples.Correctness.uint8ToUInt32Value` checks widening before `UInt32` arithmetic.  `uint32ToUInt8Wrap` checks narrowing from `300` to `44`.  These conversions stay internal because exported `UInt8` and `UInt32` values remain outside the ABI.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 134 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 134 accepted, 15 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Recursion Branch Orientation

The Nat-recursion extractor now accepts the conditional tail-call shape with the recursive call in either branch.  For `if cond then recursiveCall else exitValue`, the emitted loop continues while `cond` holds and fuel remains.  For the older `if cond then exitValue else recursiveCall` shape, the emitted loop continues while `cond` is false and fuel remains.

`LeanExe.Examples.Correctness.recThenBranchExitDemo` covers early exit from the new orientation.  `recThenBranchFuelDemo` covers fuel exhaustion in the same source shape.  Existing recursion examples still cover unconditional tail calls, let-bound recursive arguments, product-valued recursive arguments, and the original early-exit orientation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 136 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 136 accepted, 15 rejected, and 4 trapped cases`, `checked 23 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: ByteArray FNV-1a Example

`LeanExe.Examples.ByteArrayPrograms.fnv1a32` computes the 32-bit FNV-1a checksum of a read-only `ByteArray` and returns it as `UInt64` at the public ABI boundary.  The program uses internal `UInt8` reads, `UInt8.toUInt32`, internal `UInt32` xor and multiplication, and the supported fuel-recursion shape over a byte buffer.  This gives the byte-array harness a small real byte-oriented program rather than only single-byte accessors.

The JavaScript harness computes expected values with `Math.imul` and unsigned 32-bit truncation.  The cases cover empty input, one byte, and a short multi-byte input.  The Lean program remains pure and does not add byte-array construction or mutation support.

Checks run:

- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 26 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 136 accepted, 15 rejected, and 4 trapped cases`, `checked 26 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Scalar Inequality

The extractor now lowers Lean’s `!=` notation, which elaborates to `bne`.  The lowering is the negation of the same scalar equality path used for `BEq.beq`.  It works both as a `Bool` expression and directly as a condition.

`LeanExe.Examples.Correctness.bneScalars` covers `UInt64` inequality in a branch.  `bneAsBool` covers a `Bool` entry result over bounded `Nat`.  `bneBool` covers inequality over `Bool` values.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 141 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 141 accepted, 15 rejected, and 4 trapped cases`, `checked 26 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Bool.xor

The extractor now lowers `Bool.xor` through the condition extractor.  The lowering computes exclusive-or from existing condition forms: left and not right, or not left and right.  This keeps boolean normalization in the same path used by `&&`, `||`, and `!`.

`LeanExe.Examples.Correctness.boolXorValues` covers false/false, false/true, and true/true cases.  The entry returns `Bool`, so the harness checks the public boolean ABI as well as condition lowering.  No new IR operation was needed.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 144 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 144 accepted, 15 rejected, and 4 trapped cases`, `checked 26 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Safe Indexing

The extractor now lowers `GetElem?.getElem?`, the elaborated form of `a[i]?`, for `Array UInt64` and `ByteArray`.  The lowering adds extractor-level structured lets so the array pointer, byte-array pointer and length, and index are bound once around the resulting `Option` tag and payload.  The `some` payload uses the existing bounds-checked load, but consumers only evaluate that payload when the tag is nonzero, so out-of-bounds safe indexing returns `none` without trapping.

This work also fixes generated `Option` matcher arm ordering.  Generated matcher declarations pass arms in source order, so a match written with the `some` arm first does not have the same argument order as a match written with the `none` arm first.  The extractor now classifies generated `Option` matcher arms by the lambda domain: `Unit` for `none`, and the payload type for `some`.

`LeanExe.Examples.Correctness.arrayGetQuestionRead` covers in-bounds and out-of-bounds `Array UInt64` safe indexing.  `arrayGetQuestionGetDSkipsDefaultTrap` checks default laziness after safe indexing.  `arrayGetQuestionNoneSkipsPayloadTrap` checks that the out-of-bounds path does not execute the payload load.  `optionSomeFirstMatch` directly covers generated `Option` matcher arm ordering.  `LeanExe.Examples.ByteArrayPrograms.byteAtQuestionOrZero` covers safe byte indexing through the byte-array ABI.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 149 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 29 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 149 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Bool Matcher Arm Order

Generated `Bool` matcher declarations pass arms in source order.  The extractor previously assumed the generated argument order was always false arm then true arm, which only holds when the source match lists `false` first.  The extractor now reads the generated matcher type and classifies each arm by whether its result type is indexed by `Bool.false` or `Bool.true`.

`LeanExe.Examples.Correctness.boolMatchTrueFirstScalar` covers a match written with the `true` arm first.  `boolMatchTrueFirstSkipsFalseTrap` checks branch laziness in the same source order, so a reversed lowering would execute the false arm and trap.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 152 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 152 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nonrecursive Nat Matches

The extractor now lowers nonrecursive zero/successor matches over bounded `Nat` values.  Generated `Nat` matchers have a `Unit` arm for zero and a `Nat` arm for successor, so the extractor classifies source-ordered arms by binder type.  The lowering binds the scrutinee once, returns the zero arm when it is zero, and passes `n - 1` to the successor arm when it is nonzero.

`LeanExe.Examples.Correctness.natMatchZero` covers the ordinary zero-first source order.  `natMatchSuccFirst` covers successor-first source order and checks that the predecessor value reaches the successor arm.  `natMatchZeroSkipsSuccTrap` and `natMatchSuccSkipsZeroTrap` check branch laziness.  `natMatchBoolCondition` covers a `Nat` match producing `Bool`, and `natMatchProduct` covers a structured product result.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 162 accepted, 15 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 162 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Report Classifier Alignment

The checked-environment report now uses the generic entry signature checker to render entry shapes instead of a small hard-coded set of shapes.  It also classifies implemented frontier primitives for internal products, internal `Option`, erased `Unit` values used by generated matchers, safe indexing, array append and extract, fixed-width conversions, and nonrecursive `Nat` matches.  This removes rejected frontier entries from reports for declarations that the compiler already accepts.

`test/report_classification.js` covers one `Nat` matcher entry, one byte-array safe-indexing entry, and one `Option`/product entry.  Each case checks that the report shows the expected entry shape, reports an implemented compile status, and contains no rejected frontier item.

Checks run:

- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 3 report classification cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 162 accepted, 15 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Internal Unit Values

The generic compiler now admits `Unit` as an internal value type.  It represents `()` as scalar zero, accepts local `Unit` values, product fields containing `Unit`, and project-local helpers with `Unit` parameters or results.  The public ABI remains unchanged: entries with `Unit` parameters or `Unit` results are rejected.

`LeanExe.Examples.Correctness.unitProductSecond` covers `Unit` inside a product.  `unitHelperCall` covers an internal helper parameter of type `Unit`, and `unitResultIgnored` covers an internal helper result of type `Unit`.  `rejectUnitReturn` and `rejectUnitParam` keep the ABI boundary explicit.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 165 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 165 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt32 Division Coverage

The generic primitive path already lowered `UInt32` division and remainder through the same checked division and remainder operations used by `UInt64` and `UInt8`.  The specification did not state that support, and the correctness harness did not test it.  The tests now cover ordinary `UInt32` division and remainder and Lean’s zero-divisor behavior.

`LeanExe.Examples.Correctness.uint32DivMod` checks a nonzero divisor.  `uint32DivModZero` checks that `x / 0` returns `0` and `x % 0` returns `x`.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 167 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 167 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Dependent If

The extractor now lowers `dite`, the elaborated form of `if h : p then ... else ...`.  The condition uses the existing proposition extractor, and both proof-lambda arms receive an erased scalar placeholder for the proof binder.  The emitted value uses the same branch-local behavior as ordinary `if`, so skipped dependent-if arms do not evaluate partial operations.

`LeanExe.Examples.Correctness.dependentIfNat` covers a bounded-`Nat` proposition.  `dependentIfSkipsElseTrap` and `dependentIfSkipsThenTrap` check branch laziness.  `dependentIfProduct` covers a structured product result.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 173 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 173 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array Empty Constructors

The extractor now lowers `Array.empty`, `Array.mkEmpty`, `Array.emptyWithCapacity`, and `Array.singleton` for `Array UInt64`.  Empty constructors allocate an empty array.  The capacity argument is not extracted because the current array layout has no observable capacity, and Lean’s pure definitions of these constructors do not use that argument.  `Array.singleton` allocates one element through the existing replicate path.

`LeanExe.Examples.Correctness.arrayEmptyConstructors` covers the three empty constructors.  `arrayEmptyCapacitySkipsTrap` checks that an ignored capacity expression is not evaluated.  `arraySingletonRead` checks singleton size and element contents.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 176 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 176 accepted, 17 rejected, and 4 trapped cases`, `checked 29 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: ByteArray Extract

The extractor now lowers `ByteArray.extract` as an internal read-only slice.  It binds the source pointer, source length, start, and stop once, clamps stop to the source length, returns an empty slice when start is outside the source or stop does not exceed start, and otherwise returns a pointer-length view into the original bytes.  Public `ByteArray` results remain outside the ABI.

`LeanExe.Examples.ByteArrayPrograms.sliceSecondPlusSize` checks reading through a nonempty slice and the empty result when start equals the source length.  `sliceClampSize` checks stop clamping, and `sliceStopBeforeStart` checks the empty case when stop precedes start.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/bytearray_alloc.js` returned `checked 34 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 176 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat Division Coverage

The extractor already lowered `Nat` division and remainder through the checked unsigned operation path.  The specification now states that bounded `Nat` division and remainder use Lean’s zero-divisor behavior: `x / 0` returns `0`, and `x % 0` returns `x`.

`LeanExe.Examples.Correctness.natDivModNormal` checks ordinary quotient and remainder results.  `natDivModZero` checks the zero-divisor case.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 179 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 179 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Product Pattern Matching

The extractor now lowers product pattern matching for ordinary generated matchers and direct `Prod.casesOn` applications, and it recognizes `Prod.rec` if a checked term contains it.  A product matcher arm receives the left and right fields as internal values, preserving the same field-level laziness used by product projection.  The demand summary path maps demanded arm binders back to the corresponding scrutinee fields, so a helper that destructures a pair and ignores one field does not force the ignored field.

`LeanExe.Examples.Correctness.productMatchDestructure` checks ordinary pair destructuring.  `productMatchUsesFirstOnly` checks that the ignored field does not trap.  `productMatchCondition` checks a product match used as a condition, and `productMatchNested` checks a product match returning a product.

An initial parallel `node test/core_correctness.js` run raced `lake build LeanExe.Examples.Correctness` and failed before compilation because the example module’s `.olean` file was not present.  The harness passed when rerun after the example build completed.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 183 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 183 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option Fallback

The extractor now lowers `Option.orElse` and option `<|>` for internal `Option` values.  The fallback thunk receives an erased `Unit` value and is extracted only for the `none` arm.  The demand summary path treats the fallback as branch-local, so a helper that returns an existing `some` value does not force a trapping fallback.

`LeanExe.Examples.Correctness.optionOrElseNone` checks `<|>` on `none`.  `optionOrElseDirectSomeSkipsFallbackTrap` checks direct `Option.orElse` on `some` without evaluating the fallback, and `optionOrElseProduct` checks a structured payload.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 186 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 186 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option Filter

The extractor now lowers `Option.filter` for internal `Option` values.  The predicate runs only for `some`, and it receives the payload as a lazy internal value.  Filtering a `some` value to `none` leaves the payload irrelevant, matching the existing tagged representation.

`LeanExe.Examples.Correctness.optionFilterSomeKeep` and `optionFilterSomeDrop` check the two predicate outcomes for `some`.  `optionFilterNoneSkipsPredicateTrap` checks that `none` skips a trapping predicate.  `optionFilterIgnoresPayloadTrap` checks that a predicate which ignores its argument does not force a trapping payload.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 190 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 190 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Structured Helper Inlining

Nonrecursive project-local helpers now inline directly from the checked environment when their source signature uses supported local types.  This separates helper inlining from the Wasm function list, whose emitted functions still use the scalar and array ABI.  The inline stack rejects recursive inline expansion, so recursive code continues through the existing recursion path rather than expanding without a bound.

`LeanExe.Examples.Correctness.productHelperResult` checks a helper returning a product, and `productHelperParamSkipsTrap` checks a product parameter with an ignored trapping field.  `optionHelperResult` and `optionHelperNone` check a helper returning `Option`, and `optionHelperParam` checks an `Option` parameter.

The first focused harness run failed on `productHelperResult` because the inline attempt still lived only in the scalar extraction path.  The value extractor now tries local helper inlining before falling back to scalar extraction, so structured helper results enter the extractor as structured values.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 195 accepted, 17 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 195 accepted, 17 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Internal Except Values

The extractor now lowers restricted internal `Except` values.  `Except.error` uses tag `0`, `Except.ok` uses tag `1`, and each value carries both an error payload and an ok payload so pattern matching can select the demanded arm.  `Except Unit α` remains rejected because the current internal type shape also represents `Option α` as `Unit ⊕ α`; the extractor needs source type identity before those two cases can share the same payload types without ambiguity.

`LeanExe.Examples.Correctness.exceptOkMatch`, `exceptOkFirstMatch`, and `exceptErrorMatch` check constructor ordering and generated matcher arm ordering.  `exceptErrorSkipsUnusedPayloadTrap` checks payload laziness, `exceptMatchCondition` checks a match used as a condition, and `exceptProductPayload` checks a structured ok payload.  `rejectExceptReturn` and `rejectExceptParam` keep the current ABI boundary explicit.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 201 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 201 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Map and Bind

The extractor now lowers `Except.map` and `Except.bind` for restricted internal `Except` values.  Both operations evaluate their function only for the `ok` case.  `Except.bind` preserves an existing error without evaluating the bind function, and it adopts the tag and payloads returned by the bind function for `ok`.

`LeanExe.Examples.Correctness.exceptMapOk`, `exceptMapErrorSkipsFunctionTrap`, and `exceptMapProduct` check mapping over `ok`, skipped mapping over `error`, and structured mapped payloads.  `exceptBindOk`, `exceptBindErrorSkipsFunctionTrap`, `exceptBindFunctionError`, and `exceptBindProduct` cover the corresponding bind cases.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 208 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 3 report classification cases`, `checked 208 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Report Coverage for Structured Values

The report classification harness now includes entries that depend on structured helper inlining and restricted internal `Except` support.  `productHelperResult` checks an inline-only product helper signature, and `exceptBindProduct` checks the `Except` constructors, matcher, and bind classifier path.

Checks run:

- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 5 report classification cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 208 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Helper Coverage

The correctness suite now covers nonrecursive helpers with restricted `Except` parameters and results.  The specification also no longer describes structured outputs as waiting for `Except` to enter the core IR; `Except` is internal now, while public structured outputs still need a Wasm result ABI.

`LeanExe.Examples.Correctness.exceptHelperResult` and `exceptHelperError` check a helper returning restricted `Except`.  `exceptHelperParam` checks an `Except` parameter.

The first focused harness run failed on `exceptHelperResult` because the value-level `if` extractor still handled only ByteArray, product, and `Option`-shaped sum result types before falling back to scalar extraction.  The value-level `if` path now accepts every supported local result type.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 211 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 211 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except toOption

The extractor now lowers `Except.toOption` for restricted internal `Except` values.  The lowering reuses the `Except` tag as the `Option` tag and keeps only the ok payload, so an error payload is not needed when the resulting `Option` is inspected.

`LeanExe.Examples.Correctness.exceptToOptionOk` checks the ok path.  `exceptToOptionErrorSkipsPayloadTrap` checks that converting an error to `none` does not force an ignored trapping error payload.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 213 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 213 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Fallback

The extractor now lowers `<|>` for restricted internal `Except` values through `HOrElse.hOrElse`.  The fallback thunk runs only for `error`; an existing `ok` value preserves its payload without evaluating the fallback.

`LeanExe.Examples.Correctness.exceptOrElseError` checks recovery from an error, `exceptOrElseOkSkipsFallbackTrap` checks fallback laziness for `ok`, and `exceptOrElseFallbackError` checks a fallback that also returns an error.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 216 accepted, 19 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 216 accepted, 19 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Unit Rejection

The correctness suite now checks the documented rejection of `Except Unit α`.  The current internal type representation uses `Unit ⊕ α` for `Option α`, so accepting `Except Unit α` would require the extractor to preserve source type identity rather than relying on the current structural sum type alone.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 216 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 216 accepted, 20 rejected, and 4 trapped cases`, `checked 34 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except Specification Alignment

Several summary rows in `spec.md` still described only product and `Option` support after restricted `Except` entered the internal value fragment.  The summary rows now mention restricted `Except` for local lets, constructors, pattern matching, and report classification.

Checks run:

- [x] Documentation-only change; no build required.

## 2026-05-07: Proof-Indexed GetElem

The extractor now lowers `GetElem.getElem`, the checked term behind proof-indexed `a[i]` and `input[i]`.  The proof argument is erased, and the runtime load uses the same checked array or byte-array load path as partial indexing.  This lets source code use ordinary proof-indexed indexing when Lean can supply or carry the bounds proof.

`LeanExe.Examples.Correctness.arrayGetProof` checks `Array UInt64` proof-indexed reads.  `LeanExe.Examples.ByteArrayPrograms.byteAtProofOrZero` checks proof-indexed `ByteArray` reads under a dependent-if bounds proof.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `lake build LeanExe.Examples.ByteArrayPrograms`
- [x] `node test/core_correctness.js` returned `checked 217 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 36 bytearray allocation cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 217 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Pure Id Run

The extractor now erases `Id.run` and `Pure.pure` when the monad argument is `Id`.  This supports simple pure `do` blocks that elaborate to `Id.run do ... return value`.  General monadic bind, loops, and effectful `do` blocks remain outside this step.

`LeanExe.Examples.Correctness.idRunLet` checks a simple pure return.  `idRunSkipsUnusedLetTrap` checks that the existing lazy-let behavior still skips an unused trapping binding inside the `Id` block.  `idRunCondition` checks a pure `Id` block used as a condition.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 220 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 220 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Pure Id Bind

The extractor now erases `Bind.bind` when the monad argument is `Id`.  The bound value enters the continuation as a lazy internal value, matching the extractor’s existing lazy-let behavior for ignored bindings.  This supports simple pure `do` blocks with `let x ← pure value`.

`LeanExe.Examples.Correctness.idRunBind` checks a pure bind in an `Id.run` block.  `idRunBindSkipsUnusedTrap` checks that an ignored bound value does not force a trapping expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 222 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 5 report classification cases`, `checked 222 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Report Coverage for Pure Id

The report classification harness now includes `LeanExe.Examples.Correctness.idRunBind`, so the classifier checks the `Id.run`/`Pure.pure`/`Bind.bind` frontier used by simple pure `do` notation.

Checks run:

- [x] `lake build`
- [x] `node test/report_classification.js` returned `checked 6 report classification cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 222 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Simple let mut Coverage

Lean elaborates simple `let mut` assignment inside `Id.run` to ordinary shadowing lets, which the extractor already supports.  The correctness suite now covers that source style so it does not regress while pure `Id` support grows.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 223 accepted, 20 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 223 accepted, 20 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Pure Id Loop Rejection

The correctness suite now checks that a pure `for` loop inside `Id.run` remains rejected.  Lean elaborates the loop body to a function that returns `ForInStep`, which the current extractor does not lower.  This keeps the pure `do` support limited to `Id.run`, `Pure.pure`, `Bind.bind`, and let-style code.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 223 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 223 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Structured Pure Id Bind Coverage

The correctness suite now covers `Id.run do let x ← pure ...` when the bound value is a product, an `Option`, or a restricted `Except`.  The extractor already routes `Id` binds through the general value extractor, so these tests confirm that pure `do` notation preserves the existing structured-value behavior instead of only scalar bindings.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 226 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 6 report classification cases`, `checked 226 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except isOk

Lean 4.29 exposes `Except.isOk : Except ε α -> Bool`.  The extractor now lowers it for restricted internal `Except` values by reading the existing tag, so the payload of `Except.ok bad` is not extracted when the program only asks whether the value is ok.

An initial parallel `node test/report_classification.js` run raced `lake build LeanExe.Examples.Correctness` and failed because the example module’s `.olean` file was not present yet.  The report harness passed when rerun after the example build completed.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 7 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 229 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 7 report classification cases`, `checked 229 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Except mapError

Lean 4.29 exposes `Except.mapError : (ε -> ε') -> Except ε α -> Except ε' α`.  The extractor now lowers it for restricted internal `Except` values.  The mapping function runs only for `error`, and `ok` preserves its payload without evaluating the mapping function.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 8 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 232 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 8 report classification cases`, `checked 232 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: UInt64 toNat Coverage

The correctness suite now covers `UInt64.toNat` directly and through method notation.  The method-notation case uses `UInt64` maximum to check that the bounded `Nat` representation preserves the full 64-bit value at the ABI boundary.

Checks run:

- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/core_correctness.js` returned `checked 234 accepted, 21 rejected, and 4 trapped cases`.
- [x] `node test/run_all.js` returned `checked 8 report classification cases`, `checked 234 accepted, 21 rejected, and 4 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option get!

Lean 4.29 defines `Option.get!` as a panic on `none`, not as an `Inhabited` default.  The IR now has an explicit trap expression, and the extractor lowers `Option.get!` by selecting the payload for `some` and the trap expression for `none`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 9 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 237 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 9 report classification cases`, `checked 237 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Option any and all

The extractor now lowers `Option.any` and `Option.all` for internal `Option` values.  Both operations evaluate their predicate only for `some`; `any` returns false for `none`, and `all` returns true for `none`, matching Lean’s definitions.  The report classifier also recognizes `UInt64.decLt`, which appears as the decidable instance for a supported `UInt64` comparison inside an `Option.any` predicate.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 10 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 241 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 10 report classification cases`, `checked 241 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Bool toNat

The extractor now lowers `Bool.toNat`.  The current scalar representation already stores false as `0` and true as `1`, so the lowering preserves the existing expression.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 11 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 243 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 11 report classification cases`, `checked 243 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat Boolean Comparisons

The extractor now lowers `Nat.blt` and `Nat.ble` as Boolean comparisons over the bounded `Nat` representation.  This covers code that calls the named Boolean comparison functions instead of using proposition comparisons in an `if`.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 12 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 248 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 12 report classification cases`, `checked 248 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Nat Boolean Equality

The extractor now lowers `Nat.beq` as Boolean equality over the bounded `Nat` representation.  The correctness suite covers both direct Bool results and conditions that branch on the named equality function.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 13 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 252 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 13 report classification cases`, `checked 252 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array Append Notation

The extractor now lowers `HAppend.hAppend` for `Array UInt64`, so source code can use `left ++ right` instead of calling `Array.append` directly.  The lowering reuses the existing copy-on-write array append IR operation.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 14 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 253 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 14 report classification cases`, `checked 253 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array back?

The extractor now lowers `Array.back?` for `Array UInt64`.  The emitted value is an internal `Option`: empty arrays produce `none`, and nonempty arrays produce `some` with the last element.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 15 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 255 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 15 report classification cases`, `checked 255 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array modify

The extractor now lowers `Array.modify` for `Array UInt64`.  In-bounds modification reads the old element, applies the source lambda, and emits the existing copy-on-write array update.  Out-of-bounds modification returns the original array and does not evaluate the lambda.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 16 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 257 accepted, 21 rejected, and 5 trapped cases`.
- [x] `node test/run_all.js` returned `checked 16 report classification cases`, `checked 257 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array insertIdxIfInBounds

The extractor now lowers `Array.insertIdxIfInBounds` for `Array UInt64`.  The IR has a dedicated insertion expression so the emitter can evaluate the array and index first, then evaluate the inserted value only when `index <= size`.  In-bounds insertion allocates a fresh array, copies the prefix, writes the inserted value, and copies the suffix one slot to the right.  Out-of-bounds insertion returns the original array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 17 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 260 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayInsertIdxIfInBoundsSkipsValueTrap --out .lake/build/core-correctness/arrayInsertIdxIfInBoundsSkipsValueTrap.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayInsertIdxIfInBoundsSkipsValueTrap .lake/build/core-correctness/arrayInsertIdxIfInBoundsSkipsValueTrap.wat` returned `7`.
- [x] `node test/run_all.js` returned `checked 17 report classification cases`, `checked 260 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array eraseIdxIfInBounds

The extractor now lowers `Array.eraseIdxIfInBounds` for `Array UInt64`.  In-bounds erasure allocates a fresh array with one fewer element, copies the prefix, and copies the suffix one slot to the left.  Out-of-bounds erasure returns the original array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 18 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 263 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayEraseIdxIfInBoundsMiddle --out .lake/build/core-correctness/arrayEraseIdxIfInBoundsMiddle.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayEraseIdxIfInBoundsMiddle .lake/build/core-correctness/arrayEraseIdxIfInBoundsMiddle.wat` returned `132`.
- [x] `node test/run_all.js` returned `checked 18 report classification cases`, `checked 263 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array swapIfInBounds

The extractor now lowers `Array.swapIfInBounds` for `Array UInt64`.  It evaluates the array and both indices once, returns the original array when either index is out of bounds, and otherwise allocates a fresh array, copies the cells, and writes both swapped elements from the original array.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 19 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 266 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arraySwapIfInBoundsEnds --out .lake/build/core-correctness/arraySwapIfInBoundsEnds.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arraySwapIfInBoundsEnds .lake/build/core-correctness/arraySwapIfInBoundsEnds.wat` returned `4231`.
- [x] `node test/run_all.js` returned `checked 19 report classification cases`, `checked 266 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Array reverse

The extractor now lowers `Array.reverse` for `Array UInt64`.  Arrays with length zero or one return the original pointer, matching the exposed Lean definition.  Longer arrays allocate a fresh array and copy source cells in reverse order.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 20 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 268 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayReverseRead --out .lake/build/core-correctness/arrayReverseRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayReverseRead .lake/build/core-correctness/arrayReverseRead.wat` returned `321`.
- [x] `node test/run_all.js` returned `checked 20 report classification cases`, `checked 268 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.

## 2026-05-07: Proof-indexed Array updates

The extractor now lowers proof-indexed `Array.insertIdx`, `Array.eraseIdx`, and `Array.swap` for `Array UInt64`.  It erases proof arguments and reuses the existing in-bounds insert, erase, and swap operations.  The report now omits dependencies of expanded theorem declarations from the runtime frontier, so generated proof declarations do not introduce rejected external dependencies.

Checks run:

- [x] `lake build`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node test/report_classification.js` returned `checked 21 report classification cases`.
- [x] `node test/core_correctness.js` returned `checked 271 accepted, 21 rejected, and 5 trapped cases`.
- [x] `.lake/build/bin/lean-wasm compile-wat --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.arrayProofInsertIdxRead --out .lake/build/core-correctness/arrayProofInsertIdxRead.wat`
- [x] `env XDG_CACHE_HOME=.lake/build/cache .lake/build/tools/wasmtime-v36.0.9-aarch64-linux/wasmtime --invoke arrayProofInsertIdxRead .lake/build/core-correctness/arrayProofInsertIdxRead.wat` returned `123`.
- [x] `node test/run_all.js` returned `checked 21 report classification cases`, `checked 271 accepted, 21 rejected, and 5 trapped cases`, `checked 36 bytearray allocation cases`, and `checked 56 cases`.
