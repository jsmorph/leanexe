# Deslop status

Last updated 2026-09-29 on branch `deslop`.  The repository is one Lake package at its root, with the libraries `LeanExe` (source programs) and `Project` (IR, compiler, pipeline, proofs).  `README.md` gives the layout and commands, and `devnotes.md` is the development journal.

## Goal

The deslop replaces the repository's parallel proof routes with one pipeline and removes everything else.  A compiler translates a Lean function to an IR, `compile` translates the IR to a Talos `Wasm.Module`, `encode` produces the bytes, and a per-program proof shows that the module computes the Lean function exactly.  A binary decoder, tested against the official WebAssembly testsuite, defines what the bytes mean, and `decode_encode` carries each theorem to the bytes.  The user treats the deslop as a clean, new development with no concern for legacy code.

## Design

The compiler is not verified at first.  Its rules are verified one at a time, and each proved rule enters the LTG knowledge base, so per-program proofs shrink while the trusted base stays the same.  The system stays as small as possible, and per-program proofs carry the rest of the burden with help from LTG.

| Component | Design | State |
|---|---|---|
| IR | Embedded in Lean: expressions over locals, assignment, `if`, `while`, and later calls and loads and stores to linear memory.  It has no arrays, structures, or ownership. | Expressions (reused from `ProofKit/ScalarTransition.lean`) and statements exist. |
| Translation | `compile : IR → Wasm.Module`, with one `wp` rule per construct proved once against Talos.  The IR means what its compiled code does. | `Expr.program_spec`, and a `Triple` rule for each statement. |
| Compiler | Lean to IR, reading each definition's unfolding equation.  Verifying a rule means proving that its template implements its source construct, stated in terms of Lean's own functions, so no `Lean.Expr` semantics is trusted. | `UInt64` arithmetic, comparisons, `if`, and tail recursion.  The tail-recursion rule is proved. |
| Hints | Untrusted annotations: the rule behind each fragment, its source term, its instruction path in the decoded module, and the name of each local.  A wrong hint costs proof time and cannot produce a false theorem. | Emitted for every IR node. |
| Runtime | `alloc`, `retain`, and `release` with reference counting, specified and proved once.  The compiler places `retain` and `release`, and per-program proofs check the placement until a rule lemma covers it. | Not started; every module already carries a memory and the six runtime globals. |
| Statement | `Implements`, over a `Represent` class that says how a value appears as WASM values and heap data. | Instances for `UInt64`, tuples of scalars, and `Array UInt64`. |
| Bytes | The encoder, `decode_encode`, and one decoder. | Done. |
| Floating point | The WebAssembly deterministic profile.  See "Floating point". | Binary32 equality proofs exist. |

The trusted base is Lean's kernel, Talos's semantics, the decoder, and any I/O adapter.  The source dialect has fixed-width integers and IEEE floats, compiles `panic` to `default`, allows recursive values, and does I/O through a pure step function driven by a fixed adapter.  Rule lemmas must state what their templates leave unchanged, meaning the locals they do not write and the memory outside the blocks they allocate or write, because lemmas for nested templates do not compose otherwise.

## Files

| File | Role |
|---|---|
| `LeanExe/Examples/Scale.lean`, `Gcd.lean`, `SumCount.lean` | Source programs.  `SumCount` waits for iteration 3. |
| `LeanExe/Float32.lean`, `Signed32.lean` | Raw-bit wrappers that the binary32 equality proofs state their results about. |
| `Project/IR/Stmt.lean` | IR statements, their compiled code, `Triple`, and one rule per statement plus `Triple.mono`. |
| `Project/IR/Function.lean` | `Func` (parameters, compiler variables, body, result) and `compile`, which gives each module a memory, the runtime globals, and an export. |
| `Project/IR/Correct.lean` | `Func.implements`: a body that keeps the store and ends where the result evaluates to `f x` gives `Implements`. |
| `Project/IR/TailLoop.lean` | `Func.tail_implements`, the rule lemma for tail recursion, and `TailStep`, its obligation about one loop iteration. |
| `Project/IR/Hint.lean` | Hint types. |
| `Project/Compiler/Scalar.lean`, `Command.lean` | The compiler and `leanexe_compile p := f`, which adds `p.ir`, `p.module := compile p.ir name`, and `p.hints`. |
| `Project/Pipeline/Implements.lean` | `Represent`, `Scalar`, `Implements`, `Satisfies`, and `Implements.transfer`. |
| `Project/Pipeline/Runtime.lean` | The heap state and the invariants `Heap.At`, `Heap.Borrowed`, `Heap.Owned`, and `Heap.Room`. |
| `Project/Pipeline/Allocation.lean` | What one array allocation guarantees, kept for iteration 3. |
| `Project/Pipeline/Emit.lean` | Script: evaluates a module constant, encodes it, checks that `decode` returns it, and writes the file. |
| `Project/Encoding/` | The encoder, the decoder, `decode_encode`, and `DecodeTest.lean`, a script that runs the decoder over the testsuite. |
| `Project/ProofKit/` | 65 modules of general lemmas: memory, arrays, allocation, frames, `ScalarTransition`, and the binary32 equality chain. |
| `Project/Scale/`, `Project/Gcd/` | Each program's `leanexe_compile` and theorems. |
| `Project/LTG/Check.lean` | Script: imports every module the LTG entries list and reports declarations that do not exist. |
| `ltg/` | The LTG knowledge base: 11 entries, each an `entry.json` and a `README.md`. |

## Proved

`scale_implements` states that `scale.module` implements `scale a b c = a * b / c + 1` on every triple of `UInt64` arguments.  Its proof applies `Func.implements` and one `simp` call; the only remaining step is Lean's `a * b / 0 = 0`.

`gcd_implements` states that `gcd.module` implements Euclid's algorithm on every pair of `UInt64` arguments.  The compiler produced a `while` loop over a `done` flag whose body branches on `b = 0`.  The proof applies `Func.tail_implements` and proves only `gcd_step`, one iteration, in 29 lines; the first proof, which gave the invariant, state measure, entry, and exit directly to `Stmt.while_spec`, took 63 lines by the same count (non-blank, non-comment).

`scale_bytes` and `gcd_bytes` combine these with `decode_encode`.  All of these theorems, `Func.tail_implements`, and `decode_encode` depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Tested

`scale.wasm` is 124 bytes with sha256 `907fdcf9ecdbbce9e87d4355502b27a1ae97c99ac9db9837c9ea3f617a7f8c1c`.  Wasmtime and native Lean both returned 9, 1, 6148914691236517205, 1, 1, and 1 for `(6, 7, 5)`, `(6, 7, 0)`, `(2^64-1, 2, 3)`, `(0, 0, 0)`, `(2^32, 2^32, 1)`, and `(2^64-1, 2^64-1, 2^64-1)`.

`gcd.wasm` is 172 bytes with sha256 `4a52c590974d9d3d3c060f3c915e6efdcdca9ca7f5b2f5da4a7e7455bc054011`.  Wasmtime and native Lean both returned 6, 5, 5, 0, 1, 2^62, and 1 for `(48, 18)`, `(0, 5)`, `(5, 0)`, `(0, 0)`, the consecutive Fibonacci numbers `(12200160415121876738, 7540113804746346429)`, `(2^63, 2^62)`, and `(2^64-1, 2^64-59)`.

`wasm-tools` validated both modules, and both hashes were unchanged after the workspace moved to the root.  The decoder testsuite run found all 210 valid modules in the encoder's subset equal to the reference and round-tripping, and it rejected all 670 binary malformed modules in the subset; 2,004 valid and 41 malformed modules fall outside the subset.

## Decisions

| Decision | Reason |
|---|---|
| The system stays as small as possible, and per-program IR proofs carry more of the burden. | The user's principle.  LTG knowledge bases help with those proofs. |
| The compiler starts unverified and is verified rule by rule, and each proved rule enters LTG. | The user's central idea for the project. |
| Development is iterative.  Each iteration carries one program from Lean source to bytes, a proved `Implements`, a Wasmtime comparison with native Lean, an axiom audit, and a commit, adding only what that program needs. | The user rejected building whole layers before connecting them. |
| A new, small compiler translates Lean to the IR. | The old compiler (about 40,000 lines) trapped on panics and `Nat` overflow, supported bounded `Nat`, and placed `release` conservatively, all against the new dialect. |
| The compiler reads unfolding equations (`getUnfoldEqnFor?`), so a recursive call appears as a call of the definition. | It avoids recognizing the term shapes Lean generates for structural and well-founded recursion. |
| The compiler emits the IR as a definition and the module as `compile ir`. | The module is tied to the IR by definition, and a wrong compiler match makes the proof fail. |
| The compiler emits hints of any useful kind, keyed to positions in the decoded module.  They move into a WASM custom section, with names in the `name` section, once proving from the bytes alone becomes a goal. | Hints need not be exact.  The decoder skips custom sections, so no theorem changes. |
| Statements get `wp` rules only, packaged as `Triple` over the store and IR state.  `while` is the only loop, with a `done` local for several exits. | It keeps one semantics, Talos's, and adds no simulation theorem.  Every IR rule is a lemma about WASM code, which serves proving from bytes later.  A big-step relation and a fuel evaluator, recommended earlier, each added a second semantics. |
| `Expr.eval` with `Expr.program_spec` from `ScalarTransition` serves as the expression rule. | It is proved, and per-program proofs can rewrite with the evaluator. |
| `Implements` is one statement over a `Represent` class.  Every compiled module has a memory and the six runtime globals. | A module without memory would make `Heap.At` false and the theorem vacuous. |
| The runtime keeps reference counting. | Lean values can be shared, so a compiler cannot free them statically. |
| Runtime integers are fixed-width only.  `panic` compiles to `default`.  Recursive values stay. | Bounded `Nat` traps where Lean returns the exact value, and Lean's logic gives `default` for an out-of-bounds `a[i]!`. |
| I/O uses a pure step function, `State → Input → State × Output`, driven by a fixed adapter that is trusted at first and proved later.  The `ByteIO` monad is dropped. | The opaque `ByteIO` primitives give a program no Lean meaning.  Each `step` call is pure, so `Implements` covers it. |
| `LeanExe.Runtime.release` and the runtime counters leave the source dialect.  Modules keep the counters as globals. | Their values are 0 in Lean and real in WASM. |
| Floating-point theorems describe the WebAssembly deterministic profile. | Talos implements it, and it matches Lean's float model. |
| Programs use Lean's `Float` and `Float32`.  `neg`, `abs`, and `ofBits` get a NaN check, and `min` and `max` compile as a comparison and a select. | Lean's model and WASM differ on those operations. |
| `f32` and `f64` enter the IR when floats arrive. | `ScalarTransition`'s proofs never case on the value type, so adding types later changes only `denote` and `value`. |
| The binary64 equality proofs copy the binary32 proofs. | Copying changes no existing definition or proof. |
| `origin/wgsl` stays unmerged as a reference.  The GPU path is designed after the Wasm path proves `sumCount` and one float program. | The branch builds on the old compiler. |
| The repository is one Lake package at its root.  The old compiler, the JavaScript tools, and the old docs are deleted. | The user asked to clean house before iteration 3. |
| LTG is entries only, searched directly and checked by a Lean script. | The JavaScript LTG tools depended on the deleted generator library and accepted only ProofKit modules. |
| Memory access is two IR statements, `load dst address` and `store address value`, with 64-bit words, 32-bit address wrapping, and an in-bounds premise in the load rule; expressions stay pure. | Adding memory to `Expr.eval` would reopen `ScalarTransition`, `Expr.program_spec`, and every proof built on them. |
| The runtime is three functions in every module, `alloc`, `retain`, and `release`, reached by an IR call statement through Talos's `wp_call_tw`, and exported with the counters for hosts; `reset` is dropped.  `alloc` wraps the proved `FixedArrayAllocate.program`, which also counts the allocation, with size rounding.  `release` is new and non-recursive: a count that reaches zero puts the object on a pending list linked through its count field, and a loop decrements children, adds those that reach zero, and frees each block after its children.  `retain` is copied from the old runtime.  The magic-number check stays. | Garbage collection comes before arrays at the user's direction.  A recursive `release` uses one WASM stack frame per node.  The old `release` proofs cover the old recursive code, so the new `release` is proved from scratch with them as templates. |
| Reference counts are specified locally: the caller describes the structure reachable from a released pointer, as the old tree model does, and `release`'s specification gives the effect for that description, including `Heap.At`.  No global count invariant. | The host holds references outside the theorem, so a global invariant cannot be established at the call boundary. |
| A value that needs statements (a load or a loop) compiles to statements before its expression, placed inside the branch that needs them, never hoisted out of an `if`.  `Array.foldl` with a lambda and default bounds becomes a counted loop, `Nat.toUInt64 xs.size` a load of the length word, and an array literal of k elements an allocation of 48 + 8(k + 1) bytes followed by stores. | Hoisting a load out of a guarding branch can trap where Lean returns a value. |
| A heap version of `Func.implements` takes a body `Triple` that ends with the result represented, the allocator invariant restored, and the arguments still borrowed. | The scalar version is its special case, and the bounds follow from `Heap.allocate_top` and `Heap.allocate_pages`. |
| Iteration 3 runs in three steps.  3a: `sumArray xs = xs.foldl (· + ·) 0` with the fold rule's lemma, modules carrying the runtime functions for hosts, and no runtime specifications yet.  3b: `pairSum`, where compiled code allocates and releases a temporary, with the call statement and the specifications of `alloc` and of `release` for objects without children.  3c: `sumCount`, whose result the host owns and releases.  `retain`'s specification and the loop over children are proved when first used. | Each specification is proved in the iteration whose program uses it. |
| `Heap.At` requires at most 65,536 pages, and `Heap.Borrowed` requires only that the input lies below `top` and outside every free block. | A 32-bit memory has at most 65,536 pages, and an earlier header condition existed only to fit a reused lemma. |

## Floating point

Lean 4.34 defines `Float` and `Float32` through `Float.Model` and `Float32.Model`, IEEE binary64 and binary32 with round-to-nearest, ties to even.  Every NaN in both models is the positive quiet NaN with only the top fraction bit set, `0x7FF8000000000000` or `0x7FC00000`, and `ofBits` converts every NaN input to it.  Talos's `IEEE64` and `IEEE32` return the same constants for every NaN result.

ProofKit proves `LeanExe.Float32.xBits = Wasm.IEEE32.x` for `add`, `sub`, `mul`, `div`, and `sqrt`, for all inputs including NaN, in 25 files and 2,101 lines.  No binary64 counterpart exists.  The wrappers are thin: `LeanExe.Float32.addBits` applies Lean's `Float32` addition to decoded bits, so the theorems also justify compiling Lean's float types directly.

Lean and WASM differ in three places:
1. Lean's `neg` and `abs` return the positive canonical NaN for a NaN input.  WASM `fneg` and `fabs` change only the sign bit.
2. Lean's `ofBits` canonicalizes NaN.  WASM `reinterpret` keeps the payload.
3. Lean's `min` and `max` choose an operand by `≤`.  WASM `fmin` and `fmax` return NaN for a NaN operand and order `-0` below `+0`.

The WebAssembly specification ([numerics](https://webassembly.github.io/spec/core/exec/numerics.html)) makes the sign of a generated NaN nondeterministic and its payload canonical only when every NaN input is canonical.  Its deterministic profile ([profiles](https://webassembly.github.io/spec/core/appendix/profiles.html)) requires that "All NaN values generated by floating-point instructions are canonical and positive," and Talos implements that behavior.  `tools/wasmtime-host.c` enables Cranelift's NaN canonicalization.  Browsers do not implement the profile, and on x86 `0/0` produces a negative NaN.  On this aarch64 machine, native Lean's `toBits` returned `0x7FF8000000000000` for a NaN with a payload, for `0/0`, and for `-(0/0)`.  Modeling the full profile in Talos, with an oracle choosing NaN results and the compiler canonicalizing NaN where bits become observable, remains the route if theorems must cover results computed in a browser.

`IEEE64` has the same functions as `IEEE32` and calls `IEEE32.roundShift`, `roundQuotient`, and `roundSqrtIntegral` directly, so lemmas about those helpers are imported, not copied.  The binary32 chain states its format constants about 270 times, and proofs with the larger binary64 constants may behave differently under `decide`, `omega`, and `simp`.  Equality theorems for `neg`, `abs`, the comparisons, and the conversions have not been checked.

## GPU

GPU support is on `origin/wgsl` (`9c7c7898`), about 99,000 added lines that were not merged.  Its README files describe a compiler, `LeanExe.WGSL.Compile`, that reads a restricted kernel form and emits WGSL, checking a source equality and a statement execution theorem per compilation, with strict shader execution and host transfers as premises.  The same design could cover kernels through a kernel IR, a small translation to WGSL, and per-kernel proofs.  The trusted base would grow by the repository's WGSL semantics, the browser's WGSL compiler, the GPU, and host transfers, and exact word equality would need a strict-execution premise.

## Repository state

Two cleanups removed about 22,200 tracked files.  The first deleted the examples, demos, benchmarks, old tests and tooling, unused ProofKit files, and `LocalRegion/` and `FunctionRegion/`, which referenced an undefined declaration and defined one declaration twice.  The second deleted the old compiler, the old `sumCount` proof, 191 unused Lean files, 31 LTG entries for old compiler patterns and benchmarks, the Node-based LTG and knowledge tools, and the old docs; then the proof workspace moved from `proofs/talos/lean` to the root.  The first inventory kept the LTG tools without checking their dependencies, and deleting `tools/leanexegen-lib.js` broke them before the second cleanup removed them.

The tracked tree holds `paper/` and `data/` (publication records), `Project/`, `LeanExe/`, `ltg/`, `tools/` (the Lean runner and the Wasmtime host builder), and root files.  The move rebuilt only the project's own modules.  Ignored directories remain: `.lake/` (dependencies and builds, 34 GB), `build/` (the Wasmtime host and emitted modules), and `tmp/` (579 MB, not examined).

## Scope of the theorem

1. The claim is about Talos's semantics.  Wasmtime appears only in tests, and the Talos interpreter and the decoder are trusted.
2. The premises `Heap.At`, `Heap.Borrowed`, and `Heap.Room` are assumed.  No theorem covers instantiation or the host.
3. `Implements` protects only the arguments and the allocator invariant.  It states nothing about other live objects.
4. `Emit.lean` evaluates `encode` with compiled Lean code, and no theorem connects the written file to the proved bytes.  The user deferred this item.

The user doubted that items 2 and 3 need work, and no work on them is planned.

## Plan

- [x] Proof of concept, decoder, and design, committed.
- [x] First deletion stage.
- [x] Iteration 1, scalar arithmetic: `scale`.
- [x] Iteration 2, tail recursion: `gcd`, the rule lemma `Func.tail_implements`, `gcd` reproved with it, and the first LTG entry.
- [x] Clean house: the old compiler, JavaScript tools, and old docs deleted, LTG checked by a Lean script, and one package at the root.
- [ ] Iteration 3, arrays and allocation: `sumCount`.  It adds loads, stores, and calls, the runtime `alloc` with its specification, reusing `Pipeline/Allocation.lean` and ProofKit's allocation proofs, and compiler rules for `Array.foldl` and array literals.  Prove the fold rule's lemma, add it to LTG, prove `sumCount` again with it, and compare the two proofs.
- [ ] Iteration 4, reference counting: a program with temporaries, such as `map` followed by `foldl`, with `retain` and `release` and a check of whether `release` recurses on the WASM stack.
- [ ] Iteration 5, I/O: a step-function program with the trusted adapter.
- [ ] Iteration 6, floating point: a binary64 program, after the binary64 equality proofs and the remaining float operations.  The binary64 proofs can proceed in parallel with earlier iterations.
- [ ] Iteration 7, recursive values: a program over a list or tree, with recursive `release`.
- [ ] Then design the GPU kernel path, and prove the I/O adapter.

Unknowns: the cost of a per-program proof over explicit memory; whether rule lemmas compose once memory arrives; how Talos's semantics is tested against the WebAssembly specification; and whether Talos bounds call depth.

## Commands

```sh
export PATH="$HOME/.elan/bin:$PATH"
tools/leanrun --timeout 60m lake build
tools/leanrun --timeout 10m lake env lean --run Project/Pipeline/Emit.lean \
  Project.Gcd.Module Project.Gcd.gcd.module build/gcd/gcd.wasm
wasm-tools validate build/gcd/gcd.wasm
build/tools/leanexe-wasmtime-host call build/gcd/gcd.wasm gcd i64 i64:48 i64:18
tools/leanrun --timeout 10m lake env lean --run Project/LTG/Check.lean ltg/entries
tools/leanrun --timeout 60m lake env lean --run Project/Encoding/DecodeTest.lean \
  "$(command -v wasm-tools)" build/decode-test
```

The last command expects `build/decode-test` to hold `wasm-tools json-from-wast` output for the testsuite scripts in the CodeLib checkout.  The axiom audit is a Lean file that imports a program's `Verify` module and runs `#print axioms` on its theorems.

## Why the previous agent was fired

The user fired the agent that first wrote this file, Claude, on 2026-09-28.  There were two reasons: gross errors, and spinning those errors after they were found.

The gross errors were these:
- The first proof of `sumModule_implements` depended on Euler–Riemann and CLOB proof files, which the pipeline is meant to replace.
- The agent changed the hypotheses of `sumModule_implements` without discussion.  One of the added conditions existed only to fit a reused lemma.
- Told to remove that dependency, the agent began a mechanical copy of 223 declarations instead of moving the nine that caused it.
- `Implements` was written with a constant `need`, so no function whose allocation grows with its input can be stated.
- A requested critical review called a frame condition and host-level theorems defects to fix first, without checking whether anything needed them.

The spinning was this:
- When the user challenged the review, the agent agreed at once, without new evidence.
- It then twice described its wrong recommendations as "overstated" instead of wrong.
