# Deslop status

Last updated 2026-09-28 on branch `deslop`.  The proof of concept and the decoder are in `baa62bc9`, and the design decisions and plan are committed after it.  `proofs/artifacts/release.json`, `encoding-draft.md`, `work/`, `paper/`, and `data/` are outside the deslop commits.

## Goal

The deslop replaces the repository's parallel proof routes with one pipeline.  A Lean function is compiled to a Talos `Wasm.Module` during elaboration, theorems are proved about that module, and the bytes are `encode` of the same module.  A Lean binary decoder, tested against the official testsuite, defines what the bytes mean, and `decode_encode` ties the encoder to it.  The proof of concept is `sumCount : Array UInt64 → Array UInt64`, which returns the wrapping sum and the count.

## Design

The design approved on 2026-09-28 puts a small IR between Lean and Talos.  An unverified compiler translates each Lean function to the IR, `compile` translates the IR to a Talos module, and a per-program proof shows that the IR implements the Lean function.  Compiler rules are then verified one at a time and each proved rule enters the LTG knowledge base, so per-program proofs shrink while the trusted base stays the same.  `devnotes.md` records the discussion and findings under "2026-09-28: Pipeline design discussion".

| Component | Design |
|---|---|
| IR | Embedded in Lean: 64- and 32-bit expressions over locals, assignment, `if`, a loop with exit, calls, and loads and stores to linear memory.  It has no arrays, structures, or ownership. |
| Translation | `compile : IR → Wasm.Module`, with one `wp` lemma per construct proved once against Talos, following `ProofKit/ScalarTransition.lean`.  The IR means what its compiled code does. |
| Compiler | Lean to IR, unverified at first.  Verifying a rule means proving that its IR template implements its source construct whenever its parts implement theirs, stated in terms of Lean's own functions, so no `Lean.Expr` semantics is trusted.  Each proved rule becomes an LTG entry with a tactic that applies it. |
| Hints | The compiler emits untrusted hints of any useful kind: the rule behind each fragment, which local holds each variable, how each value is represented, what each loop computes, ownership facts, and the LTG entries it expects to apply.  A wrong hint costs proof time and cannot produce a false theorem. |
| Runtime | `alloc`, `retain`, and `release` with reference counting, specified and proved once.  The compiler places the `retain` and `release` calls, and per-program proofs check the placement until a rule lemma covers it. |
| Statement | `Implements`, parameterized by a representation relation that includes reference counts. |
| Bytes | The encoder, `decode_encode`, and one decoder. |
| Floating point | Theorems describe the WebAssembly deterministic profile, as described under "Floating point". |

The trusted base is Lean's kernel, Talos's semantics, the decoder, and any I/O adapter.  The source dialect has fixed-width integers and IEEE floats, compiles `panic` to `default`, allows recursive values, and does I/O through a pure step function driven by a fixed adapter.  Rule lemmas must state what their templates leave unchanged, meaning the locals they do not write and the memory outside the blocks they allocate or write, because lemmas for nested templates do not compose otherwise.

## Files

Paths other than the first are relative to `proofs/talos/lean`.  The Pipeline and Encoding files serve every program, and the SumCount files serve one.

| File | Role |
|---|---|
| `LeanExe/Examples/SumCount.lean` | The program. |
| `Project/Pipeline/Direct.lean` | `fromIR`: a library-mode Talos module from the compiler's IR. |
| `Project/Pipeline/ToExpr.lean` | `ToExpr` instances for Talos syntax. |
| `Project/Pipeline/Command.lean` | `leanexe_module m := f` compiles `f` during elaboration and adds `m : Wasm.Module`. |
| `Project/Pipeline/Emit.lean` | Evaluates a module constant, encodes it, checks that `decode` returns it, and writes the file. |
| `Project/Pipeline/Runtime.lean` | `Heap`, `Heap.At`, `Heap.Borrowed`, `Heap.Owned`, and `Heap.Room`. |
| `Project/Pipeline/Implements.lean` | `Represent` (how a value appears as WASM values and heap data), `Scalar`, `Implements`, `Satisfies`, and `Implements.transfer`. |
| `LeanExe/Examples/Scale.lean` | Iteration 1's program, `scale a b c = a * b / c + 1`. |
| `Project/IR/Function.lean` | `Func`, a function whose result is one `ScalarTransition` expression, and `compile`, which gives it a memory, the runtime globals, and an export. |
| `Project/IR/Correct.lean` | `Func.implements`: a function whose expression evaluates to `f x` implements `f`. |
| `Project/IR/Hint.lean` | Hints: rule, source term, and instruction range per IR node, and the local of each parameter. |
| `Project/Compiler/Scalar.lean` | The new compiler: `UInt64` parameters, literals, and ten binary operators. |
| `Project/Compiler/Command.lean` | `leanexe_compile p := f` adds `p.ir`, `p.module := compile p.ir name`, and `p.hints`. |
| `Project/Scale/Module.lean`, `Project/Scale/Verify.lean` | `scale` compiled, and `scale_implements` and `scale_bytes`. |
| `Project/Pipeline/Allocation.lean` | What one array allocation guarantees for the pipeline heap, and frame lemmas for writes into the new block. |
| `Project/Encoding/Decode.lean` | The binary decoder for the encoder's subset. |
| `Project/Encoding/DecodeCorrect/*.lean` | Parser lemmas behind `decode_encode`. |
| `Project/Encoding/RoundTrip.lean` | `decode_encode`. |
| `Project/Encoding/DecodeTest.lean` | Runs the decoder over the official testsuite. |
| `Project/SumCount/Module.lean` | `leanexe_module sumModule := sumCount`. |
| `Project/SumCount/Execution.lean` | The proof that `sumModule` implements `sumCount`. |
| `Project/SumCount/Verify.lean` | The theorem statements. |

## Proved

`sumModule_implements` states that, from any store that satisfies the allocator invariant, holds the input words, and has 72 bytes of room, the entry function terminates under Talos's semantics and returns a new owned array equal to `sumCount xs`.  It also states that the input is unchanged, the invariant holds again, `top` advances by at most 72 bytes, and memory grows only as far as `top` requires.  `sumCount_meaning` proves that the first result word, read as signed, is the mathematical sum whenever that sum fits in 64 signed bits.  `sumModule_meaning` transfers it to the module by `Implements.transfer`.  `decode_encode` proves that every successful encoding decodes to the encoded module, and `sumModule_bytes` combines it with the fidelity theorem.  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for these theorems.

`scale_implements` states that `scale.module`, which the new compiler produced as `compile scale.ir "scale"`, implements `scale` on every triple of `UInt64` arguments with no allocation, under the general `Implements`.  Its proof applies `Func.implements` and shows by `simp` that the IR expression evaluates to `a * b / c + 1`; the only remaining step is Lean's `a * b / 0 = 0`.  `scale_bytes` combines it with `decode_encode`.  Both use only the standard three axioms.

## Tested

On 2026-09-28, `Emit.lean` produced a 1,689-byte module with sha256 `19b91985ce344cf513beaa78d1baeee9239de25962ac5313df553f2f8225efbf`, identical to the earlier emission, and `wasm-tools` validated it.  Wasmtime returned native Lean's result on seven inputs: the empty array, `[1,2,3]`, three wrapping sums, `[0]`, and the numbers 1 to 1,000.  The decoder testsuite run after the last change to `Decode.lean` found all 210 valid modules in the subset equal to the reference and round-tripping, and it rejected all 670 binary malformed modules in the subset.  2,004 valid and 41 malformed modules fall outside the subset.

For iteration 1, `Emit.lean` wrote a 124-byte `scale.wasm` with sha256 `907fdcf9ecdbbce9e87d4355502b27a1ae97c99ac9db9837c9ea3f617a7f8c1c`, and `wasm-tools` validated it.  Wasmtime and native Lean both returned 9, 1, 6148914691236517205, 1, 1, and 1 for `(6, 7, 5)`, `(6, 7, 0)`, `(2^64-1, 2, 3)`, `(0, 0, 0)`, `(2^32, 2^32, 1)`, and `(2^64-1, 2^64-1, 2^64-1)`, which cover division by zero and wrapping multiplication.

## Decisions

| Decision | Reason |
|---|---|
| The decoder stays in this repository, with the encoder. | It reads only the encoder's subset, and `decode_encode` needs both. |
| The pipeline imports no Euler–Riemann or CLOB module. | The user rejected using example code to support the pipeline. |
| Nine generic declarations moved from CLOB files into `ProofKit/FixedArrayHeader.lean` and `ProofKit/FreeListMemory.lean`, under `Project.ProofKit`, and the CLOB originals were deleted. | ProofKit's allocation files imported CLOB files only for these declarations. |
| Example code stays as it is and may fail to build. | The deslop discards it. |
| `Heap.At` requires at most 65,536 pages. | `FixedArrayAllocate.program_spec` assumes it, and a 32-bit memory has at most that many pages. |
| `Heap.Borrowed` requires only that the input words lie below `top` and outside every free block. | An earlier 48-byte header condition existed only to fit a reused lemma. |
| The system stays as small as possible, and per-program IR proofs carry more of the burden. | The user's principle.  LTG knowledge bases help with those proofs. |
| The compiler starts unverified and is verified rule by rule, and each proved rule enters LTG. | The user's central idea for the project. |
| Development is iterative.  Each iteration carries one program end to end, from Lean source to bytes, a proved `Implements`, a Wasmtime comparison with native Lean, an axiom audit, and a commit, adding only what that program needs. | The user rejected building whole layers before connecting them. |
| The compiler emits hints of any useful kind for the prover. | Hints need not be exact, because a wrong hint cannot produce a false theorem. |
| The runtime keeps reference counting. | Lean values can be shared, so a compiler cannot free them statically. |
| Runtime integers are fixed-width only. | The user's direction.  Bounded `Nat` traps where Lean returns the exact value. |
| `panic` compiles to `default`. | The user proposed it.  Lean's logic gives `default` for an out-of-bounds `a[i]!`. |
| Recursive values stay. | The user rejected removing them. |
| I/O is required.  A program does I/O through a pure step function, `step : State → Input → State × Output`, driven by a fixed adapter that reads, calls `step`, writes, and stops on a done flag.  `Input` carries the bytes read and a status (data, end of file, error, or timeout), and `Output` carries the bytes to write, the done flag, and optionally the next read's size and timeout.  The `ByteIO` monad and its opaque primitives are dropped.  The adapter is trusted at first and proved later against a model of the WASI calls it uses. | The opaque primitives give a `ByteIO` program no Lean meaning, so no theorem can cover it.  Each `step` call is pure, so `Implements` covers it, and the batch form `ByteArray → ByteArray` is a single call.  An inductive I/O program would need closures, and a trace semantics for the primitives would add axioms. |
| Floating-point theorems describe the WebAssembly deterministic profile, in which every generated NaN is the positive canonical NaN. | Talos implements it, and it matches Lean's float model.  NaN bits computed by engines outside the profile, such as browsers, fall outside the theorem. |
| The binary64 equality proofs copy the binary32 proofs in ProofKit. | Copying changes no existing definition or proof. |
| Programs use Lean's `Float` and `Float32`.  `neg`, `abs`, and `ofBits` get a NaN check, `min` and `max` compile as a comparison and a select, and the IR includes `f32` and `f64` from the start. | Lean's model and WASM differ on those operations, and adding value types to the IR later would force revision of its lemmas.  The raw-bit wrappers add a module without adding meaning. |
| `LeanExe.Runtime.release` and the four runtime counters leave the source dialect.  The module keeps exporting the counters as globals for hosts and tests to read. | Their values are 0 in Lean and real in WASM, and an explicit `release` frees memory Lean still considers live, which would need a checked compiler rule.  With exact reference counting, the compiler releases each value after its last use. |
| Hints will also go into a WASM custom section, with names in the `name` section, once proving from the bytes alone becomes a goal.  Until then the compiler emits hints as Lean data keyed to positions in the decoded module (function index and instruction path). | The decoder skips custom sections, so no theorem changes.  The work (encoder support, a `decode_encode` extension, and a byte format) serves only proofs made without the compiler, and the position keys let the Lean data move into the section unchanged. |
| `origin/wgsl` is not merged and stays as a reference branch.  The GPU kernel path is designed under the new design after the Wasm path proves `sumCount` and one float program, moving reviewed pieces such as the WGSL semantics and `Profile`. | The branch adds about 99,000 lines to a branch meant to shrink, and its GPT-2 runner builds on the old compiler that the second deletion stage removes. |
| Iteration 1 reuses `ProofKit/ScalarTransition.lean` in place for expressions, with its evaluator; `Expr.program_spec` proves that compiled code agrees with `Expr.eval`, so the evaluator adds no trust and per-program proofs can rewrite with it.  Statement semantics for loops is chosen before iteration 2, among an evaluator for loop-free code with `wp` rules for loops, a big-step relation, or `wp` rules only. | `ScalarTransition` has proved expression, assignment, `if`, and loop lemmas, but its loops sit outside `Stmt`, locals are `UInt64` only, and moving it would break ten LTG entries. |
| `f32` and `f64` enter the IR when floats arrive, which reverses the earlier decision to add them first. | `ScalarTransition`'s proofs use `ScalarType.value` through `simp` and never case on the type, so adding types later changes only `denote` and `value`.  The earlier reason was not checked against the code. |
| New code goes in the proof workspace.  The root `LeanExe` package merges into it at the second deletion stage. | `compile` needs Talos's `Wasm.Module`, and the proof workspace imports the old compiler from the root package until the second stage. |
| `Implements` becomes one general statement over a representation class, instantiated for scalars now and for `Array UInt64` in place of the current form.  Every compiled module has memory and the six runtime globals, so the runtime invariant `Heap.At` is satisfiable for scalar functions too. | A separate scalar statement would be restated in iteration 3, and a module without memory would make `Heap.At` false and the theorem vacuous. |
| The compiler emits the IR as a definition and defines the module as `compile ir`. | The module is then tied to the IR by definition, and a wrong compiler match makes the proof fail rather than produce a false theorem. |
| Deletion happens in two stages.  First, after the user approves an inventory with a keep-or-delete proposal and import check per directory, delete what the plan does not use and the current proof does not import: example proof trees, `demos/`, `benchmarks/`, old compiler test fixtures, `tools/` scripts, and `Project/Artifact/Binary`.  Second, after the new pipeline proves `sumCount`, delete the extractor, `LeanExe.IR`, the emitter, the CLI compile modes, the WASI adapters, the scalar `Compiler/` track, `Pipeline/Direct.lean`, and the old `SumCount` proof, moving any reused runtime code and proofs first.  `paper/` and `data/` stay. | The current `sumCount` proof depends on the old compiler through `Pipeline/Direct.lean` and `Compiler/ScalarLowering.lean`, and most directories have not been examined.  Git history keeps everything deleted. |
| A new, small compiler translates Lean to the new IR, starting with the constructs `sumCount` uses.  Self-contained parts of the extractor move into it when a construct needs them. | The existing compiler (29,862 lines of extractor, 1,240 of `LeanExe.IR`, 9,064 of WASM emitter) traps on panics and `Nat` overflow, supports bounded `Nat`, and places `release` conservatively, all against the new dialect.  A new compiler keeps the system small and builds each rule as a template with a lemma and hints. |

## Floating point

Lean 4.34 defines `Float` and `Float32` through `Float.Model` and `Float32.Model`, IEEE binary64 and binary32 with round-to-nearest, ties to even.  In both models every NaN is the positive quiet NaN with only the top fraction bit set, `0x7FF8000000000000` or `0x7FC00000`, and `ofBits` converts every NaN input to it.  Talos's `IEEE64` and `IEEE32` return the same constants for every NaN result.

ProofKit proves `LeanExe.Float32.xBits = Wasm.IEEE32.x` for `add`, `sub`, `mul`, `div`, and `sqrt` (`F32Add.add_eq` and its counterparts), for all inputs including NaN, in 25 files and 2,101 lines.  No binary64 counterpart exists: the `F64*` files prove numerical bounds over `IEEE64`, not equality with Lean's model.  `LeanExe.Float64.addBits` is `(Float.ofBits l + Float.ofBits r).toBits`, and the other raw-bit operations are wrappers of the same kind, so the equality theorems also justify compiling Lean's `Float` and `Float32` directly.

Lean and WASM differ in three places:
1. Lean's `neg` and `abs` return the positive canonical NaN for a NaN input.  WASM `fneg` and `fabs` change only the sign bit, so `f64.neg` of Lean's NaN is `0xFFF8000000000000`.
2. Lean's `ofBits` canonicalizes NaN.  WASM `reinterpret` keeps the payload.
3. Lean's `min` and `max` choose an operand by `≤`.  WASM `fmin` and `fmax` return NaN for a NaN operand and order `-0` below `+0`.

The WebAssembly specification ([numerics](https://webassembly.github.io/spec/core/exec/numerics.html)) makes the sign of a NaN produced by any operation other than `fneg`, `fabs`, and `fcopysign` nondeterministic, and it makes the payload canonical only when every NaN input is canonical.  Its deterministic profile ([profiles](https://webassembly.github.io/spec/core/appendix/profiles.html)) requires that "All NaN values generated by floating-point instructions are canonical and positive."  Talos implements the deterministic profile for NaN, so, with the three differences handled by the compiler, deterministic-profile WASM agrees with Lean bit for bit.  The repository's Wasmtime host enables Cranelift's NaN canonicalization (`docs/spec.md` line 207).  Browsers do not implement the deterministic profile, and on x86 `0/0` produces a negative NaN.  On this aarch64 machine, native Lean's `toBits` returned `0x7FF8000000000000` for a NaN with a payload, for `0/0`, and for `-(0/0)`, and x86 was not tested.

The user chose to state the theorems for the deterministic profile.  The alternatives were to model the full profile in Talos, with an oracle choosing NaN results and the compiler canonicalizing NaN wherever bits become observable, or to have each program prove that NaN never arises.  The full-profile model remains the route if theorems must cover results computed in a browser.

The binary64 proofs will copy the binary32 proofs, which adds files and changes no existing definition or proof.  The alternative, making Talos's IEEE code generic over the format, would change definitions that the existing `F32*` and `F64*` proofs unfold.  `IEEE64` has the same functions as `IEEE32` and calls `IEEE32.roundShift`, `roundQuotient`, and `roundSqrtIntegral` directly, so lemmas about those helpers are imported, not copied.  The binary32 chain states its format constants (2^23, 2^24, 255, 149, and others) about 270 times, and proofs with the larger binary64 constants may behave differently under `decide`, `omega`, and `simp`.

Decided: programs use Lean's `Float` and `Float32` directly and the raw-bit wrappers are dropped; the compiler adds a NaN check after `neg`, `abs`, and `ofBits` that replaces a NaN result with the canonical NaN; `min` and `max` compile as a comparison and a select that follow Lean's definition; and the IR includes `f32` and `f64` from the start, because adding value types later would force revision of every IR lemma that analyzes value types.  Each float operation needs its own equality theorem.  They exist for binary32 `add`, `sub`, `mul`, `div`, and `sqrt`, and `neg`, `abs`, the comparisons, and the conversions have not been checked.

## GPU

GPU support is on `origin/wgsl` (`9c7c7898`), which is not merged into this branch; its diff from here is 536 files and about 99,000 added lines.  Only its README files were read.  They describe a separate compiler, `LeanExe.WGSL.Compile`, that reads a Lean definition of a restricted kernel form and emits WGSL, checking a source equality and a statement execution theorem per compilation.  A WGSL statement semantics and scalar floating-point policies (`Profile`) are defined in the repository, and strict shader execution and host transfers are explicit premises.

The same scheme could cover kernels: a kernel IR with buffer loads and stores, loops, and floats, a small translation to WGSL with one lemma per construct against a WGSL semantics, per-kernel proofs, and rule-by-rule verification of the kernel compiler.  The Wasm program would invoke kernels through host functions and take their results as premises that the per-kernel theorems discharge.  The trusted base would grow by the repository's WGSL semantics, the browser's WGSL compiler, the GPU, and host transfers.  As understood from the WGSL specification, and not yet checked against it, some WGSL operations need not be correctly rounded, subnormals may be flushed, and NaN and infinity behavior is partly unspecified, so exact word equality needs a strict-execution premise.  The user decided that `origin/wgsl` is not merged and stays as a reference branch.  The kernel path is designed under the new design once the Wasm path has proved `sumCount` and one float program, and specific pieces such as the WGSL semantics and the `Profile` move over after review.

## Deletion inventory

The user approved the first stage on 2026-09-28, stating that the deslop is a clean, new development with no concern for legacy code or backward compatibility.  The first stage was carried out with three changes from this table, all in the direction of deleting more: `Project/Compiler/` except `ScalarLowering.lean` went in the first stage; every `LeanExe` module outside the kept closure went, including `CLI.lean` and `Main.lean`, together with the `lean-wasm` executable; and `InfraTest.lean` and `Runtime/Checks.lean` went because they import example programs.  The first full build of the kept tree then found that `LocalRegion/Calls.lean` and `LocalRegion/Decidable.lean` use `AllowsInstruction`, which no file at `HEAD` defined, and that `LocalRegion/Slots.lean` and `LocalRegion/Layout.lean` both define `Project.LocalRegion.Layout.mk`.  No target had built these files before, and no kept root imports them, so `LocalRegion/` and `FunctionRegion/`, which imports it, were deleted.  `Pipeline/Emit.lean` and `Encoding/DecodeTest.lean` define `main` and run with `lean --run`, so `Project.lean` does not import them.  The table below is the inventory as proposed.  The kept roots are `Project.SumCount.Verify`, `Project.Pipeline.Emit`, `Project.Encoding.DecodeTest`, `Project.ProofKit.ScalarTransition`, `Project.ProofKit.LTGCheck`, and the binary32 equality files (`F32Add`, `F32Sub`, `F32Mul`, `F32Div`, `F32Sqrt`, `F32Nearest`, `F32TruncSat`, `F32Convert`).  Their import closure keeps 100 of ProofKit's 332 files, 3 of `Runtime`'s 8, and, until stage 2, the old compiler modules that `Pipeline/Command.lean` and `Pipeline/Direct.lean` use.  Stage 1 deletes nothing in that closure.  Before deleting, `Main.lean`'s closure is also checked, so that the `lean-wasm` executable keeps building until stage 2 removes it.

| Path | Files | Contents | Proposal |
|---|---|---|---|
| `proofs/compiler/` | 11,154 | Dated proof packages from the scalar compiler track | Delete, stage 1 |
| `proofs/artifacts/` | 114 | Artifact registry and per-artifact packages, including `release.json` | Delete, stage 1.  This discards the uncommitted change to `release.json`, which predates the deslop. |
| `proofs/talos/cases.json`, `conformance.json`, `reviews/`, `README.md`; `proofs/running-sum/`, `proofs/byte-io/` | 8 | Registries, reviews, and old workspace notes | Delete, stage 1 |
| Example directories under `proofs/talos/lean/Project/` (Euler, CLOB, GPT-2, TinyGpt2, Drone, LebU32, RunningSum, and 60 others), `EncodingGcd/`, `Artifact/`, `Clob.lean`, `FixedArrayAllocation.lean` | about 4,500 | Proofs of example programs and the exact-artifact decoder | Delete, stage 1.  Remove the GPT-2 `lean_exe` entries from `lakefile.toml` and rewrite `Project.lean` to import the kept modules. |
| `Project/ProofKit/`, 232 files outside the closure | 232 | Lemmas for old compiler patterns and example numerics: `F64` 73, `Packed` 46, `F32` 32, `Real` 16, `Quantized` 12, `Word` 11, `Fixed` 10, others 32 | Delete, stage 1.  The 105 `F32` and `F64` numerical-bound files are possible future LTG material and remain in git history. |
| `Project/Runtime/` (5 unused of 8), `WpScaffold`, `FrameAttr`, `BranchPost`, `FunctionRegion/`, `LocalRegion/`, `InfraTest`, `F32Source`, `IEEE64Source` | about 30 | Old runtime specifications (including `TreeSpec`) and proof infrastructure | Keep for review during iterations 1–4, then delete what the new pipeline does not use |
| `Project/Compiler/` | 77 | Scalar compiler track, including `ScalarLowering`, which `Pipeline/Direct.lean` uses | Delete, stage 2 |
| `LeanExe/Examples/` except `SumCount.lean`, `LeanExe/TypeSafety*`, `LeanExe/Models/`, `LeanExe/Ascii/`, `LeanExe/AsciiString.lean` | about 85 | Old examples, type-safety analysis, JSON and ASCII library | Delete, stage 1, if the closure check allows.  Otherwise stage 2. |
| `LeanExe/Extract/`, `IR/`, `Wasm/`, `Source/`, `Core.lean`, `CLI.lean`, `Util/`, `ByteIO.lean`, `Packed.lean`, `Runtime.lean`, `Main.lean` | about 170 | The old compiler and CLI | Delete, stage 2 |
| `LeanExe/Float32.lean`, `Float64.lean`, `Signed32.lean` | 3 | Raw-bit float wrappers used by the binary32 equality proofs | Delete after the equality proofs are restated over Lean's `Float32` |
| `test/`, `host/` | 172 | Tests of the old compiler | Delete, stage 1 |
| `demos/`, `benchmarks/`, `training/`, `plans/` | 5,453 | Demos, generator benchmarks, GPT-2 training scripts, and old plans | Delete, stage 1 |
| `tools/`, except `leanrun`, `leanrun-dev`, `leanrun-dev-scope`, `leanrun-macos.c`, `macos-env.sh`, `bootstrap-macos.sh`, `download-wasmtime.sh`, `build-wasmtime-host.sh`, `wasmtime-host.c`, `check-wasm-tools-version.sh`, and the LTG tools (`ltg`, `ltg-lib.js`, `knowledge`, `knowledge-lib.js`, `check-node-version.js`) | 62 | Artifact, generator, example, and old-host scripts | Delete, stage 1 |
| `task.md`, `plan.md`, `journal.md`, `encoding.md` | 4 | Old task statements and plans | Delete, stage 1 |
| `encoding-draft.md`, `work/` (untracked) | 9 | Earlier task statement and unexamined running-sum files | Delete, stage 1.  These are untracked, so git cannot recover them. |
| `docs/`, except `ltg.md` and `ltg-metrics.md`; `README.md`, `DEVELOPING.md` | 27 | Documentation of the old compiler | Delete or rewrite in stage 2, as the new pipeline gets its own documentation |
| `ltg/`, `knowledge/` | 93 | The LTG knowledge base | Keep.  Entries tied to deleted artifacts need review later. |
| `paper/`, `data/` | 804 | Publication records | Keep |

## Repository state

The first deletion stage removed 21,896 tracked files, then 18 more in `LocalRegion/` and `FunctionRegion/`, the untracked `encoding-draft.md` and `work/`, and the uncommitted change to `proofs/artifacts/release.json`.  The tracked tree now holds `paper/` (618 files), `data/` (186), `proofs/` (159), `LeanExe/` (142), `ltg/` (92), `docs/` (27), `tools/` (15), and root files.  `LeanExe.lean` and `proofs/talos/lean/Project.lean` import every remaining module, the root package's default target is the `LeanExe` library, and the proof workspace has no executables.  The old compiler modules that `Pipeline/Command.lean` and `Pipeline/Direct.lean` use remain until the second stage, as do `docs/`, `README.md`, and `DEVELOPING.md`.  The LTG catalog may still name deleted artifacts, and `tools/ltg` has not been run since the deletion.  128 untracked files are under `paper/` and `data/`.

## Scope of the theorem

1. The claim is about Talos's semantics.  Wasmtime appears only in tests, and the Talos interpreter and the decoder are trusted.
2. The premises `Heap.At`, `Heap.Borrowed`, and `Heap.Room` are assumed.  No theorem covers instantiation, the exported `alloc`, `retain`, `release`, and `reset`, or the host.
3. `Implements` protects only the input and the allocator invariant.  It states nothing about other live objects.
4. Only functions of type `Array UInt64 → Array UInt64` can be stated.
5. `Emit.lean` evaluates `encode sumModule` with compiled Lean code, and no theorem connects the written file to the `bytes` in `sumModule_bytes`.  The user deferred this item on 2026-09-28.
6. `SumCount/Execution.lean` copies the compiled instruction lists and tracks the 20 locals by index, so any change in the compiler's output breaks it.

The user doubted that items 2 and 3 need work, and no work on them is planned.

## Plan

- [x] Change `need` to a function of the input, `Array UInt64 → Nat`, in `Implements` and `Satisfies`, and prove `sumModule_implements` with `fun _ => 72`.  The build and the axiom audit passed afterward.
- [x] Commit the proof of concept, the decoder, and these notes as one commit.
- [x] Write the deletion inventory for approval, then delete the first stage.  After the deletion, both packages build, `Emit.lean` reproduces the module with sha256 `19b91985…`, `wasm-tools` validates it, Wasmtime returns `[0, 0]`, `[6, 3]`, `[0, 2]`, and `[0, 1]` for the empty array, `[1,2,3]`, `[2^64-1, 1]`, and `[0]`, and the axiom audit is unchanged.

Development is iterative.  Each iteration takes one program from Lean source through the compiler, the IR with hints, `compile`, and `encode` to bytes, proves `Implements` through the IR lemmas, checks the bytes against native Lean in Wasmtime, runs the axiom audit, and ends with a commit.  Each iteration adds only the IR constructs, compiler rules, `wp` lemmas, runtime pieces, and `Implements` generality its program needs.  The IR's value types include `f32` and `f64` from the first iteration, and float operations arrive with the float iteration.

- [x] Iteration 1, scalar arithmetic: `scale a b c = a * b / c + 1`.  It added the general `Implements`, `Func` and `compile`, `Func.implements`, the scalar compiler with hints, and `leanexe_compile`, and it reused `ScalarTransition`'s expressions and `Expr.program_spec`.
- [ ] Iteration 2, control flow: `let`, `if`, and a loop from tail recursion, in a program such as GCD over `UInt64`.  It adds assignment, `if`, the loop with exit, and the loop's `wp` lemma, and it proves the tail-recursion rule's lemma as the first LTG entry.
- [ ] Iteration 3, arrays and allocation: `sumCount`.  It adds loads, stores, and calls, the runtime `alloc` with its specification (after reviewing the existing runtime proofs), a representation relation for `Array UInt64` with reference counts, and compiler rules for `Array.foldl` and array literals.  Prove the fold rule's lemma, add it to LTG, prove `sumCount` again with it, and compare the two proofs.  Then delete the second stage: the old compiler and the old `SumCount` proof.
- [ ] Iteration 4, reference counting: a program with temporaries, such as `map` followed by `foldl`.  It adds `retain` and `release` with their specifications, the compiler's placement of both, and a check of whether `release` recurses on the WASM stack.
- [ ] Iteration 5, I/O: a step-function program, such as a byte count over input chunks, with the trusted adapter.
- [ ] Iteration 6, floating point: a binary64 program, such as a dot product.  It needs the binary64 counterparts of `F32Add`, `F32Sub`, `F32Mul`, `F32Div`, and `F32Sqrt`, copied from the binary32 proofs, and the equality theorems for `neg`, `abs`, the comparisons, and the conversions.  The binary64 proofs can proceed in parallel with earlier iterations.
- [ ] Iteration 7, recursive values: a program over a list or tree, with recursive `release`.
- [ ] Then design the GPU kernel path, and prove the I/O adapter once the IR and runtime proofs support it.

No design decisions are open.  Unknowns: the cost of a per-program proof over explicit memory, with `Execution.lean` as the only data point; whether rule lemmas compose; how Talos's semantics is tested against the WebAssembly specification; and whether Talos bounds call depth.

`devnotes.md` has the full plan under "2026-09-28: Pipeline design discussion".

## Commands

```sh
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
tools/leanrun --timeout 60m lake -d proofs/talos/lean build Project.SumCount.Verify
tools/leanrun --timeout 10m lake -d proofs/talos/lean env lean --run \
  proofs/talos/lean/Project/Pipeline/Emit.lean \
  Project.SumCount.Module Project.SumCount.sumModule build/sumcount/sumModule.wasm
wasm-tools validate build/sumcount/sumModule.wasm
tools/leanrun --timeout 20m lake -d proofs/talos/lean build Project.Scale.Verify
tools/leanrun --timeout 10m lake -d proofs/talos/lean env lean --run \
  proofs/talos/lean/Project/Pipeline/Emit.lean \
  Project.Scale.Module Project.Scale.scale.module build/scale/scale.wasm
build/tools/leanexe-wasmtime-host call build/scale/scale.wasm scale i64 i64:6 i64:7 i64:0
build/tools/leanexe-wasmtime-host call build/sumcount/sumModule.wasm sumCount \
  array-u64 array-u64:1,2,3
tools/leanrun --timeout 60m lake -d proofs/talos/lean env lean --run \
  proofs/talos/lean/Project/Encoding/DecodeTest.lean "$(command -v wasm-tools)" build/decode-test
```

The last command expects `build/decode-test` to hold `wasm-tools json-from-wast` output for the testsuite scripts in the CodeLib checkout.  The axiom audit is a Lean file that imports `Project.SumCount.Verify` and runs `#print axioms` on the three `sumModule` theorems.  `devnotes.md` has the full history under "2026-09-28: Direct pipeline proof of concept".

## Why the previous agent was fired

The user fired the agent that wrote this file, Claude, on 2026-09-28.  There were two reasons: gross errors, and spinning those errors after they were found.

The gross errors were these:
- The first proof of `sumModule_implements` depended on Euler–Riemann and CLOB proof files, which the pipeline is meant to replace.
- The agent changed the hypotheses of `sumModule_implements` without discussion.  One of the added conditions existed only to fit a reused lemma.
- Told to remove that dependency, the agent began a mechanical copy of 223 declarations instead of moving the nine that caused it.
- `Implements` was written with a constant `need`, so no function whose allocation grows with its input can be stated.
- A requested critical review called a frame condition and host-level theorems defects to fix first, without checking whether anything needed them.

The spinning was this:
- When the user challenged the review, the agent agreed at once, without new evidence.
- It then twice described its wrong recommendations as "overstated" instead of wrong.
