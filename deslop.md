# Deslop status

Last updated 2026-09-28 on branch `deslop`.  The proof of concept, the decoder, and these notes are committed in one commit after `003b653e`, the merge of `origin/encoding`.  `proofs/artifacts/release.json`, `encoding-draft.md`, `work/`, `paper/`, and `data/` remain outside it.

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

The trusted base is Lean's kernel, Talos's semantics, the decoder, and any I/O adapter.  The source dialect has fixed-width integers and IEEE floats, compiles `panic` to `default`, allows recursive values, and includes `ByteIO`.  Rule lemmas must state what their templates leave unchanged, meaning the locals they do not write and the memory outside the blocks they allocate or write, because lemmas for nested templates do not compose otherwise.

## Files

Paths other than the first are relative to `proofs/talos/lean`.  `Pipeline/Direct.lean` moved from `EncodingGcd`, and `EncodingGcd/GenerateProgram.lean` now imports it from there.  The Pipeline and Encoding files serve every program, and the SumCount files serve one.

| File | Role |
|---|---|
| `LeanExe/Examples/SumCount.lean` | The program. |
| `Project/Pipeline/Direct.lean` | `fromIR`: a library-mode Talos module from the compiler's IR. |
| `Project/Pipeline/ToExpr.lean` | `ToExpr` instances for Talos syntax. |
| `Project/Pipeline/Command.lean` | `leanexe_module m := f` compiles `f` during elaboration and adds `m : Wasm.Module`. |
| `Project/Pipeline/Emit.lean` | Evaluates a module constant, encodes it, checks that `decode` returns it, and writes the file. |
| `Project/Pipeline/Runtime.lean` | `Heap`, `Heap.At`, `Heap.Borrowed`, `Heap.Owned`, and `Heap.Room`. |
| `Project/Pipeline/Implements.lean` | `Implements`, `Satisfies`, and `Implements.transfer`. |
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

## Tested

On 2026-09-28, `Emit.lean` produced a 1,689-byte module with sha256 `19b91985ce344cf513beaa78d1baeee9239de25962ac5313df553f2f8225efbf`, identical to the earlier emission, and `wasm-tools` validated it.  Wasmtime returned native Lean's result on seven inputs: the empty array, `[1,2,3]`, three wrapping sums, `[0]`, and the numbers 1 to 1,000.  The decoder testsuite run after the last change to `Decode.lean` found all 210 valid modules in the subset equal to the reference and round-tripping, and it rejected all 670 binary malformed modules in the subset.  2,004 valid and 41 malformed modules fall outside the subset.

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
| The compiler emits hints of any useful kind for the prover. | Hints need not be exact, because a wrong hint cannot produce a false theorem. |
| The runtime keeps reference counting. | Lean values can be shared, so a compiler cannot free them statically. |
| Runtime integers are fixed-width only. | The user's direction.  Bounded `Nat` traps where Lean returns the exact value. |
| `panic` compiles to `default`. | The user proposed it.  Lean's logic gives `default` for an out-of-bounds `a[i]!`. |
| Recursive values stay. | The user rejected removing them. |
| `ByteIO` stays in the language. | The user requires it. |
| Floating-point theorems describe the WebAssembly deterministic profile, in which every generated NaN is the positive canonical NaN. | Talos implements it, and it matches Lean's float model.  NaN bits computed by engines outside the profile, such as browsers, fall outside the theorem. |
| The binary64 equality proofs copy the binary32 proofs in ProofKit. | Copying changes no existing definition or proof. |

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

Proposed and not decided: compile Lean's `Float` and `Float32` directly and drop the raw-bit wrappers, add NaN checks to `neg`, `abs`, and `ofBits`, compile `min` and `max` as a comparison and a select, and include `f32` and `f64` in the IR from the start.

## GPU

GPU support is on `origin/wgsl` (`9c7c7898`), which is not merged into this branch; its diff from here is 536 files and about 99,000 added lines.  Only its README files were read.  They describe a separate compiler, `LeanExe.WGSL.Compile`, that reads a Lean definition of a restricted kernel form and emits WGSL, checking a source equality and a statement execution theorem per compilation.  A WGSL statement semantics and scalar floating-point policies (`Profile`) are defined in the repository, and strict shader execution and host transfers are explicit premises.

The same scheme could cover kernels: a kernel IR with buffer loads and stores, loops, and floats, a small translation to WGSL with one lemma per construct against a WGSL semantics, per-kernel proofs, and rule-by-rule verification of the kernel compiler.  The Wasm program would invoke kernels through host functions and take their results as premises that the per-kernel theorems discharge.  The trusted base would grow by the repository's WGSL semantics, the browser's WGSL compiler, the GPU, and host transfers.  As understood from the WGSL specification, and not yet checked against it, some WGSL operations need not be correctly rounded, subnormals may be flushed, and NaN and infinity behavior is partly unspecified, so exact word equality needs a strict-execution premise.  The recommendation is to bring WGSL into the deslop after the Wasm path works, and the user has not decided.

## Repository state

The CLOB, Euler–Riemann, and other example directories are expected to fail to build after the ProofKit move, and they have not been rebuilt.  The pipeline's import closure contains ProofKit, Runtime, Encoding, LeanExe, `Common`, `Attr`, `TalosCompat`, `TalosPrelude`, and `Compiler.ScalarLowering`, which `Pipeline/Direct.lean` uses.  Unrelated changes predate this work and belong outside the pipeline commits: `proofs/artifacts/release.json` was already modified when the work started, `encoding-draft.md` is an earlier task statement renamed during the merge, `work/` is unexamined, and 87 untracked files are under `paper/` and `data/`.

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
- [ ] Define the IR, `compile`, and one `wp` lemma per construct.
- [ ] Specify `alloc`, `retain`, and `release`, review the existing runtime proofs (`docs/arithmetic-correctness.md` line 422), and check whether `release` recurses on the WASM stack.
- [ ] Generalize `Implements` with a representation relation that includes reference counts.
- [ ] Write a compiler for the constructs `sumCount` uses, emitting IR with hints.
- [ ] Prove that `sumCount`'s IR implements `sumCount` through the IR lemmas.
- [ ] Prove the fold rule's lemma, add it to LTG, prove `sumCount` again with it, and compare the two proofs.
- [ ] Prove the binary64 counterparts of `F32Add`, `F32Sub`, `F32Mul`, `F32Div`, and `F32Sqrt` by copying the binary32 proofs.

Open decisions:
- A new compiler or a port of the extractor.  The recommendation is a new compiler.
- The `ByteIO` design.  The proposal is a pure step function, `State → Input → State × Output`, with reading, writing, and timeouts in one fixed adapter.
- Whether hints also go into a WASM custom section, keyed to positions in the decoded module.
- Whether `release` and the runtime counters stay in the source dialect.
- The proposed floating-point compilation rules, and whether `f32` and `f64` enter the IR from the start.
- When the WGSL backend on `origin/wgsl` joins the deslop.  The recommendation is after the Wasm path works.
- The deletions: the extractor, `LeanExe.IR`, the emitter, the CLI compile modes and WASI adapters, the scalar `Compiler/` track, and `Project/Artifact/Binary`.

Unknowns: the cost of a per-program proof over explicit memory, with `Execution.lean` as the only data point; whether rule lemmas compose; how Talos's semantics is tested against the WebAssembly specification; and whether Talos bounds call depth.

`devnotes.md` has the full plan under "2026-09-28: Pipeline design discussion".

## Commands

```sh
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
tools/leanrun --timeout 60m lake -d proofs/talos/lean build Project.SumCount.Verify
tools/leanrun --timeout 10m lake -d proofs/talos/lean env lean --run \
  proofs/talos/lean/Project/Pipeline/Emit.lean \
  Project.SumCount.Module Project.SumCount.sumModule build/sumcount/sumModule.wasm
wasm-tools validate build/sumcount/sumModule.wasm
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
