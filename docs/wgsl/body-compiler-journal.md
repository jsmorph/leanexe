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

`build/gpt2/body-generation-v5/results.json` now records six successful body
compilations, with four audited proof declarations each: source equality,
actual-text parsing, statement execution, and the existing GPT-2 packed product.
The sizes include the 3,072-term projection and both 25,129/25,128-column heads.
The new build path uses these Lean definitions instead of `Generate.lean`.
Both hosts select the `lean_kernel` entry point from the new bundle metadata.

The local bundle was updated only after all six generation checks passed; its
previous template files were retained under `build/gpt2/template-backup-before-body`.
The rebuilt native runner executed `The purpose of science is` with 24 greedy
output tokens on SwiftShader's Vulkan CPU. The complete 9,649,536-byte trace
matches the previous trace exactly: 24 token IDs and 50,257 binary64 logit words
per token. The output text also matches. Evidence is in
`build/gpt2/body-execution-comparison.json`, with the trace, completion and run
log beside it. This is a regression observation, not a full GPT-2 proof or a
universal runtime-conformance result. Independent checks of the six installed
shader texts are running separately from generation.

The installed bundle independently passed
`tools/artifact-proof.js wgsl-gpt2-check build/gpt2/bundle`; the receipt is
`build/gpt2/shader-checks/check-dQN1GV/verification.json`. It checks all six
existing shader texts against their Lean bodies and packed product roles,
with four audited proof declarations per shader, and checks all fifty matrix
assignments. The receipt explicitly leaves runtime conformance and complete
model composition unestablished.

After the helper-expansion and source-proof changes, the full bounded compiler
corpus was repeated in `build/wgsl/body-check-TFeJqN`. All nine source/parse/
execution triples pass, the saved matrix proof rechecks independently, all 51
CPU output words match the original Lean reference, both operation mutations
change output, and all eighteen negative cases reject without an emitted
package. Native compilation also passes `-Wall -Wextra -Werror`; host syntax,
shell syntax and 149 maintained Markdown files pass their checks.

The browser archive was rebuilt and its six shaders and host were compared
with the installed bundle. Browser inference was not rerun in this iteration;
the actual completion test used the native CPU path. Generated shaders, Wasm,
weights, proof fragments, reports, binaries and archives remain uncommitted.

## Review: literal validity and runtime assumptions, 2026-09-17

The review found that any UInt32 word was accepted as a literal, although
`bitcast<f32>(...u)` is a WGSL constant expression and NaN/infinity constants
are shader-creation errors under the pinned WGSL specification. Before the
fix, `build/wgsl/review-20260917/Probe.lean` successfully compiled positive
infinity and a quiet NaN. Native SwiftShader/wgpu execution even accepted the
infinity shader and preserved its bits. This is evidence that a passing CPU
test alone did not enforce the standard's constant-expression restriction.

`Source.FiniteLiteral` now checks the exponent field. Both source validation
and the kernel-checked `Statement.Prim.Valid` predicate require it. The
checker also rejects an unused nonfinite literal in an existing shader.
The shared execution proofs required no new axioms or changed conclusions.
The source specification now states the complete external assumption: word
preservation through literals, loads, copies and stores, plus the modeled
operation order and arithmetic. Matching add/mul alone is insufficient.

The bounded corpus passed in `build/wgsl/body-check-TTw4Ba`: eleven source,
parse and execution proof triples; 63 exact CPU output words compared with
original Lean definitions; 24 rejection cases with no emitted packages; and
an independent replay of the matrix certificate. New positives exercise a
constant-only shader and a shader using only A. New negatives cover both
infinities, quiet/signaling NaNs, an unused NaN, and an altered Nat typeclass
instance. This last case confirms that the source-equality gate rejects the
extractor's tentative interpretation when the original instance changes the
meaning. The targeted Lean build and host syntax checks also passed.

## Review: vocabulary proof connection, 2026-09-17

The GPT-2 checker reported `vocabularyDecompositionProved: true` on the new
body-compiler path, while its composition theorem audit still referred to
`vocabulary_exact`, whose premises use the legacy template dispatch model.
The six individual packed-product proofs were present, but there was no
checked application composing the new vocabulary shader executions. Reusing
the receipt field without that connection was incorrect.

`MatrixView.columnAccum_slice` now proves the source-ordered slice identity
for any arithmetic. `bodyColumn_eq` applies a body-compiler certificate to
a packed product; `vocabulary_from_body_shaders` then proves the declared
`vocabularyBodyRun` composition for every token below 50,257. It checks the
local right column and the shifted output address. It does not claim to
verify a C or JavaScript host schedule. The driver replays both head
certificates in a single Lean file and audits the resulting specialized
composition theorem before reporting success, on both generation and checking.

The first targeted build failed because `omega` saw `UInt32.size` as an
uninterpreted constant in a range proof. Exposing its value with
`change col < 4294967296` solved that obligation; deprecated `if_pos`/`if_neg`
uses were also removed. The second targeted build passed without warnings in
the changed proof modules. Logs are `build/wgsl/review-20260917/vocabulary-build.log`
and `vocabulary-build-v2.log`.

The installed-shader gate then passed in
`build/gpt2/shader-checks/check-NRdyF3/verification.json`. All six shader
texts passed their four audited certificates, and the additional
`Project.Gpt2.CheckedVocabularyBodies` theorem passed with only `propext`,
`Classical.choice` and `Quot.sound`. Its proof replays both head certificates
without invoking the compiler. The receipt names `vocabularyBodyRun` as its
composition semantics. The fifty matrix assignments also passed. Runtime
conformance and full model composition remain explicitly unestablished.

No shader operations or runtime hosts changed in this review, and no new
completion run is claimed. The existing completion evidence remains one
24-token native greedy run after the previous shader migration, with its full
trace equal to the previous baseline. Browser inference was not rerun.
