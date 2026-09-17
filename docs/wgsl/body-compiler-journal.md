# Body compiler development journal

## First implementation, 2026-09-17

The original implementation selected a fixed GEMM template. It did not read
Lean function bodies, and the earlier description as a body compiler was
false. This implementation is separate: it traverses elaborated expressions,
recognizes only a documented arithmetic/index/fold grammar, and makes Lean
check a per-definition equality to the extracted tree.

Initial builds caught reserved identifiers and command-elaborator API mistakes.
Those were ordinary compiler errors, not proof failures. The first extraction
run compiled addition and multiplication but rejected the elaborated UInt32
zero in the two folds. Recognizing the elaborated literal before unfolding its
representation fixed this. All four equality theorems then checked, depending
only on `propext`.

The source operation mutation is material: two elementwise definitions and two
fold definitions differing at the arithmetic operation produced different
shader computations and different outputs. All four executed on the existing
native SwiftShader Vulkan CPU route. Their 24 output words matched the original
Lean definitions evaluated with the pure integer-defined IEEE32 operations.
Intermediate shaders, vectors and execution reports are ignored under
`build/wgsl/body-v1/`; no generated artifact is committed.

This checkpoint does not claim a proof about emitted text or arbitrary WebGPU
devices. The next check will parse actual emitted WGSL independently and make
the source equality refer to that parsed computation.

## Independent shader checking

Added a separate token parser for the structured WGSL grammar. It checks the
declarations, edge guard, local scopes, arithmetic, complete fold control and
final output store. The source equality now refers to the computation obtained
by parsing the actual emitted shader, not the emitter's input tree.

The first proof attempt failed because `Except` did not supply the required
decidable equality. That attempt also exposed a gating bug: default asynchronous
Lean elaboration could report a theorem error after the command had already
written its output. The failed drafts remain under `build/wgsl/body-v2/`; they
are not accepted evidence. The compiler now checks synchronously, rejects any
reported error, and audits all theorem axioms before creating the output
directory. Negative artifact tests confirm no package is written on failure.

A direct `rfl` reduction of the entire shader parser reached recursion and
heartbeat limits. Raising the recursion allowance alone did not solve it.
The fix was a reusable composition lemma joining separately checked lexer and
token-parser reductions, using `decide +kernel` as in the existing artifact
workflow. No native-computation axiom is used. The eight-case combined run
still reached its 90-second process limit, so the driver now checks each case
in a separate bounded invocation and stops on the first failure. Failed
evidence remains under `body-check-nnruHL` and `body-check-2G6dB3`.

`build/wgsl/body-check-dYiQRh/summary.json` records eight passing source and
actual-shader proofs, 48 matching CPU WebGPU output words, two operation-mutation
pairs and twelve rejection cases. `additional-checks.json` in that same
directory records two more rejections (changed loop count and initial word)
and an independent check of the saved matrix proof in a fresh Lean process,
without invoking the compiler. Those two rejections and the independent check
are included in the repeatable driver. The eight positive cases include
transparent helpers, transposed indexing, nested folds and a zero-iteration
fold with a nonzero initial word.

Source-equality proofs use `propext`; shader-parse proofs use only `propext`,
`Classical.choice` and `Quot.sound`. The implementation rejects other axiom
dependencies, including `sorryAx`. Native device conformance, the formal
soundness of the index checker and generalized memory/dispatch proofs remain
outside these established claims, as specified in the source contract.

## 768-term accumulation and final checks

Added `matmul768`, a 1×768 by 768×3 multiplication whose body uses the same
general `Source.fold` operation. Both source-equality and actual-shader parse
proofs passed, and all three CPU WebGPU words matched the original definition
under pure IEEE32 arithmetic. Evidence is in `build/wgsl/body-768/`. Combined
with the earlier corpus this is nine definitions and 51 matching output words.
The repeatable corpus now includes this case as well.

After the successful corpus, source-equality failure was made an immediate
stop before spending time on shader-parse proofs. The compiler also checks
output-directory freshness before proof work and applies the existing 64 KiB
UTF-8 artifact-check limit. The 768-term case exercised this final successful
path; focused rejection checks cover the earlier stop. No unrelated regression
suite was run and no generated shader, proof, vector or log was committed.

The final integrated `node tools/wgsl/body-test.js` run passed in
`build/wgsl/body-check-29xE6I/`: nine definitions, all eighteen source/parse
theorem audits, 51 matching output words, fourteen expected rejections, both
source-operation mutation pairs and the independent matrix-proof recheck.
This run exercised the committed compiler and the complete updated driver;
the subsequent edits only clarify normalization behavior and record this
result. The documentation checker passed for all 149 maintained Markdown files.

## 2026-09-17: statement execution proof

Added a statement AST which retains immutable bindings, scoped loop bodies,
initializer references and continuations. Added an interpreter with checked
local reads, finite input buffer extents, wrapping u32 index operations, and
explicit loop condition/counter/accumulator transitions. Exhausting an active
loop's iteration budget is an error. The new `Code.run_eq` theorem proves that
validated statement programs return the corresponding source-model value;
it covers arbitrary nesting and all scalar arithmetic interpretations.

`Index.bound_le` proves the existing interval computation bounds every accepted
index. `Index.word_eq` proves its u32 evaluation equals the natural evaluation.
The statement proof uses these facts for checked buffer loads. These modules
passed `tools/leanrun --timeout 60s lake build LeanExe.WGSL.StatementProof` as
part of the larger invocation build. Diagnostic iterations exposed missing
binder annotations, reserved constructor names, exception simplification and
loop-invariant normalization; those proof errors were repaired before this
checkpoint. Whole-shader integration is still in progress at this checkpoint;
no claim of WebGPU driver verification or GPT-2 migration follows from it.

The parser now retains statement syntax, and the mandatory compiler gate emits
and audits `wgslExecutionCorrect : Statement.Implements ...` in addition to the
parse and source-equality theorems. The whole-invocation semantics executes the
u32 guard, scoped statements and checked final store. Coverage of the rounded
8×8 grid and disjoint output addresses are also proved. No interleaved scheduler
or external-driver conformance theorem is claimed for this new grammar.

The integrated run in `build/wgsl/body-check-o6A1aP/summary.json` passed all nine
source/parse/execution proof triples, rechecked the saved matrix proof in a
fresh process, and executed all nine shaders on SwiftShader's Vulkan CPU.
All 51 words matched the original Lean definitions under pure IEEE32 arithmetic.
Eighteen negative cases rejected without creating a package. Four newly added
cases check wrong loop increments, nonzero counter starts, assignment to the
wrong accumulator and use of a local after its scope ended. The manifest is
now version 2 and explicitly identifies `Statement.runShader` as the execution
semantics. This result does not migrate the GPT-2 bundle's fixed templates.

## GPT-2 body compilation

Added six eligible Lean definitions in `LeanExe.WGSL.Gpt2`, each calling a
shared dense-product function whose callback specifies the scalar operations
and packed indices. `Project.Gpt2.BodyCompile` proves that these definitions
compute the existing packed GPT-2 matrix specification, and composes that
fact with any successful body-compiler execution certificate.

The first generation attempt, `build/gpt2/body-generation-v1`, failed before
emitting the QKV package: weak-head normalization expanded the transparent
`dense` helper past `Source.fold`, producing a chain of operations that hit
the traversal budget. The compiler now exposes one helper definition at a
time before falling back to weak-head normalization, so its loop translator
can see the fold. The failure is retained. The matrix bridge module passes;
the corrected generation in `build/gpt2/body-generation-v2` has checked its
first QKV package, including all four axiom reports. Remaining shapes and
runtime integration are still being checked at this checkpoint.

The 3,072-term projection exposed a second limitation in
`body-generation-v2`: direct reflexivity reached the proof recursion limit
while comparing the source with the statement interpretation. The failed
source declaration contained Lean's error placeholder; the synchronous error
gate stopped compilation before creating that package. The proof generator now
first simplifies statement interpretation and local-slot lookups, leaving the
fold and its callback intact. A focused 3,072-term diagnostic passed with a
4,096 recursion limit, and the complete projection package in
`body-generation-v5/3` passes all four dependency audits.

Two intervening attempts are also retained: v3 failed to compile a tactic
quotation because its identifiers needed explicit syntax categories; v4 failed
because Lean theorem headers cannot infer a placeholder type from the proof
body. The fourth product proof remains a checked proposition-valued definition
with a style warning; it is audited exactly like the three named theorems.
Neither failed attempt was installed into the demo bundle.
