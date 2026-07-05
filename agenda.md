# Development Agenda

The nine-item language agenda in [Development Plan](plan.md) is complete, differential testing runs routinely, and three Talos artifact proofs check generated modules end to end.  What remains open is the center of the plan: the formal ladder from `extract_correct` through verified passes to a composed `compile_correct`, together with a memory model whose release policy still leaks recursive temporaries by design.  This agenda orders the next work so that each step either starts that ladder or removes friction that would otherwise tax every later step.  Items marked as open questions are design decisions to settle in discussion before implementation.

## Priority 1: A Fragment-Level Lowering Theorem

The three Talos proofs each cost a handwritten development, and each breaks whenever codegen changes a byte.  The structural fact that makes a better position reachable is that the compiler, the IR interpreter, and the Talos WASM model are all Lean developments in or adjacent to this repository.  That makes Stage 4 of the correctness strategy, `wasm_lower_correct`, provable as ordinary Lean work: for every IR program in a defined fragment, the emitted module, read in the Talos model, computes what `Expr.eval` computes.

The fragment should start where the artifact proofs already succeeded: scalar functions built from locals, 64-bit arithmetic, conditionals, lets, calls, and the loop form, which covers GCD and the order book.  The first deliverable is a precise definition of that IR fragment and a statement of the theorem against the Talos semantics.  The second is the proof for straight-line programs, then loops via the invariant-and-measure structure the GCD proof already demonstrates in the concrete.  The third is re-deriving the GCD and order-book artifact theorems as corollaries, which converts two brittle proofs into regression checks of the general theorem.

One design question gates this work.  The current path runs emitter output through `wasm-tools print` and Talos WAT decoding before a Lean module value exists, so the theorem would need a lemma connecting the emitter's module representation to the decoded one, or the toolchain should produce the Talos-model module directly from the compiler's own `Wasm` module value and validate the byte-level artifact separately.  The second route shortens the trusted path and removes `wasm-tools` from the proof loop, but it changes what the checked-in proof inputs mean.  This choice should be settled first.

## Priority 2: Harden the Talos Workflow

Independent of the general theorem, the existing proof workspace has friction worth removing now because every future proof pays it.  Regenerating `Program.lean` after a compiler change is a manual step outside `tools/check-talos*.sh`; the scripts should invoke the Talos emitter so that a compiler change produces a fresh model and a clear proof failure rather than a byte-mismatch dead end.  The association-list proof hard-codes the concrete heap addresses of the sample list cells, so any change to allocation order rewrites the proof; an abstract heap predicate ("a well-formed list of these pairs exists at some root") would survive layout changes and is the shape any input-dependent allocation proof will need anyway.  The workflow documents `leanexe-talos.md` and `leanexe-talos-assoc-list.md`, along with `strings.md`, sit untracked in the working tree and should be committed or folded into the tracked documentation.

## Priority 3: The IR Interpreter as a Third Differential Semantics

`tools/compare-standard.js` compares standard Lean execution against Wasmtime, which detects errors but does not localize them: a mismatch could live in extraction or in emission.  The IR interpreter in `LeanExe/IR/Core.lean` is an executable semantics sitting exactly at the boundary the future proofs will use, and running it as a third column in the comparison harness would split every failure into a front-end or back-end fault.  This also forces the interpreter to stay total and faithful over the whole accepted corpus, which is a prerequisite for using `Expr.eval` as the specification in Priority 1 and later in `extract_correct`.  The cost is modest: a CLI mode that evaluates the compiled IR on supplied inputs, plus harness support in the comparison tool.

## Priority 4: Memory Accounting and Ownership Expansion

The conservative release policy is sound but silent about its cost: ordinary recursive heap temporaries may leak, and nothing currently measures how much.  The first step is measurement, not new analysis.  The runtime already exposes `allocCount`, `releaseCount`, and `freeCount`, so the correctness and refcount suites can record per-case allocation balances and the repository can state which programs run leak-free and which retain garbage.  With that baseline, extend the ownership summaries to prove more recursive releases safe, starting with the shapes the accounting shows are the dominant leaks; the fold-accumulator replacement rule is the template for how such a rule is stated and tested.  The unverified safety condition on source-level `LeanExe.Runtime.release` belongs on the proof ladder eventually, but a checked static approximation (rejecting releases whose value has a visible live alias) would raise assurance sooner.

## Priority 5: Language Track

Runtime `String` is the largest planned language feature, already staged in [Strings](strings.md): document the layout and ABI, add classification with string-specific diagnostics, lower literals, equality, append, `isEmpty`, and `toUTF8`, then `fromUTF8?` validation, then heap-bearing containers, then `Char` and `String.Pos`.  The plan is sound and the steps are small; the main sequencing question is whether it precedes or follows Priority 1, since every new lowering enlarges the surface a fragment theorem must eventually cover.  Starting `String` after the straight-line scalar theorem exists would let the new lowerings target the proved fragment's discipline from the beginning.

Two further language items remain from the plan's own lists and should stay behind `String` unless a concrete program needs them: a public ABI for recursive data, which requires a serialization decision at the boundary, and cross-module specialization, which extends the classifier to imported transparent bodies and concrete instances.  Both are substantial and neither blocks the correctness work.

## Engineering Hygiene

`LeanExe/Extract/Core.lean` remains a 7,154-line mutual block after five documented splits, and `LeanExe/Wasm/Binary.lean` concentrates the module model, binary encoder, WAT printer, runtime, and five WASI adapters in 6,155 lines.  The next natural split is the backend: the module model and encoder, the runtime generation, and the WASI adapters have few mutual dependencies and would separate cleanly, which matters once Priority 1 needs the emitter as a proof subject rather than a black box.  `devnotes.md` currently mixes newest-first entries at the top with appended entries at the bottom; one convention should win.  There is no performance suite; a small fixed benchmark set (Collatz, JSON pipeline, tree rewrite) with recorded Wasmtime timings would catch regressions once release insertion grows more aggressive.

## Sequencing

| Order | Work | Depends on | Outcome |
|-------|------|-----------|---------|
| 1 | Talos workflow hardening, commit untracked docs | nothing | Proof maintenance stops being manual |
| 2 | Settle the model-construction question (WAT decode vs direct module value) | discussion | Statement of the fragment theorem |
| 3 | IR interpreter in the differential harness | nothing | Fault localization; interpreter validated as specification |
| 4 | Straight-line scalar lowering theorem, then loops | 2 | `wasm_lower_correct` for the first fragment; GCD and order book as corollaries |
| 5 | Leak accounting in the test suite | nothing | Measured memory behavior across the corpus |
| 6 | Targeted recursive release rules | 5 | Fewer leaks under the same soundness discipline |
| 7 | Runtime `String` first slice | ideally 4 | Largest planned language feature, built against a proved fragment |
| 8 | Backend module split, devnotes convention, benchmarks | nothing | Lower cost for everything above |

## Open Questions

Three decisions need discussion before the corresponding work starts.  First, the Priority 1 model question: whether the fragment theorem speaks about the WAT-decoded Talos module, with a connection lemma to the emitter, or about a model built directly from the compiler's module value, with byte-level validation kept as a separate check.  Second, whether `extract_correct` (Stage 2) should wait until the lowering theorem exists, or whether defining the semantics of the extractable Lean subset should begin in parallel; the lowering-first order recommended here reflects that the IR side has an interpreter today while the Lean-subset semantics does not exist yet.  Third, for the eventual public recursive ABI, whether the boundary encoding is JSON, as the examples already practice, or a binary layout; that decision shapes both the ABI documentation and the host tooling and should not be made incidentally.
