# Incorporating the completed parent GPT-2 result into WGSL

Prepared 2026-09-18 against parent `origin/main` at
`f4d412b709a13bb2649fe23be267ec9928838064` and WGSL at
`8bec6ea9d7e34d273554e7d3ce22817564be6fa2`.

The parent was fetched and inspected. It contains 79 commits since the shared
ancestor `fa676032667ce76c6a8710af0f0522ad69341f2b`, changing 382 files.
The working branch now includes that revision. Both proof baselines and three
full-model execution comparisons passed locally; the integration journal records
the evidence. The remaining milestones below are not established by that merge.

## What the parent now establishes

`Project.Gpt2CachedStep.Spec.cachedStep_exact` proves termination and exact
cache/logit bytes for the generated cached-step Wasm module against
`LeanExe.Models.Gpt2.cachedStep`. It covers the embedding, twelve transformer
blocks, final normalization, vocabulary projection, allocation and cleanup.
Rejected inputs return empty outputs with the store unchanged.

`Project.Gpt2CachedStep.Spec.gpt2_128_exact`, in `Session/Spec.lean`, starts
from module initialization, reset, weight allocation and encoded weight bytes.
It composes token calls, previous-cache release, logit reads and logit release.
Its explicit input conditions are:

- exactly 497,759,232 weight bytes;
- each supplied token below 50,257;
- at most 128 supplied tokens.

There is no weight-value bound. The session proof derives the heap and
allocation premises needed by each step. Its output is the trace of the
Lean cached recurrence for the supplied token list. Tokenization and choosing
the next token from logits are outside that theorem.

The parent also proves `LeanExe.Float32.addBits`, `subBits`, `mulBits`,
`divBits` and `sqrtBits` agree with Talos's binary32 operations for all words.
The immediate bridge to our arithmetic is `Project.ProofKit.F32Add.add_eq`
and `Project.ProofKit.F32Mul.mul_eq`.

The parent records a successful source-artifact gate, 86 FP32 cases, all
6,432,896 logits across 128 contexts, invalid-input/reset checks and three
completions. Wasmtime uses canonical NaNs. The theorem and those execution
tests have distinct scopes: native runtime correctness, tokenization and
token selection are outside the Lean execution proof.

## Architectural decision

Use the parent's packed FP32 `cachedStep` as the common algorithm specification
and retained Wasm reference implementation. Keep this branch's restricted Lean
body compiler and shader certificates. Connect them to the parent operations
with exact word and packed-byte theorems, then develop the hybrid execution
proof at the matrix-call boundary.

The current demo's `Project.Gpt2.Model` uses binary64 non-matrix stages,
binary32 matrix products, conversions and a different cache layout. It cannot
inherit the parent's FP32 proof. Migrate those stages to the parent model and
its packed representation. Preserve the existing demo as a regression reference
during that migration.

The existing WGSL compiler accepts `Source.Kernel` pointwise definitions with
explicit arithmetic, buffer reads and bounded folds. It does not accept the
parent's complete `ByteArray → ByteArray` tensor functions. Initially compile
ordinary definitions in the supported kernel form and prove their relationship
to `linearRows` and `vocabularyHead`. Describe that interface exactly. Direct
compilation of the parent's packed-array definitions would require a separate,
specified compiler extension and additional source-equality checks.

## 1. Merge the parent and establish the shared baseline

Resolve the previewed conflicts deliberately:

| File | Resolution |
| --- | --- |
| `proofs/talos/lean/Project/ProofKit/F32Packing.lean` | Keep the parent's source-Float32 packing module at this path. Move the WGSL branch's numerical packing lemmas into `F32PackingBounds.lean` with a distinct namespace; update `F32AddBounds`, `F32DyadicBounds` and their references. Preserve both developments. |
| `tools/gpt2` | Provide explicit Wasm and WGSL launchers. Preserve the current `build/run/serve/test` invocations through compatibility routing and the parent's plain `--text` interface. Document which implementation each command selects. |
| `plans/gpt2-124m.md` | Preserve the completed parent proof record and link this integration plan as separate pending work. |

Run the parent's `tools/talos-proof.js check gpt2_cached_step` gate, the WGSL
body corpus and the installed six-shader check. Build the two consumers of the
renamed packing lemmas to catch the namespace conflict resolution. Lean/Lake
commands remain sequential through `tools/leanrun`; use the repository drivers
directly where they invoke it internally.

Acceptance: both the unchanged parent result and the WGSL certificates pass
in the merged checkout. Commit and push this baseline before backend changes.

## 2. Connect compiled kernels to the parent source

Define the scalar interpretation using the parent's `Float32.addBits` and
`mulBits`. Prove it equals the existing `Binary32.arithmetic` using the new
parent theorems. Prove that our ascending fold matches the parent's source
range reduction, preserving every operand and operation order.

Add the packed-input and packed-output connections using the parent's
`PackedSource`, `PackedWordRead` and related byte-array lemmas. The four layer
products need the final FP32 bias addition that `linearRows` performs after
the dot product. A concrete supported kernel can read its bias from B after
the matrix words at `inner * cols + col`; prove the corresponding matrix-plus-
bias view of the parent weight buffer. Generate the shader by compiling that
Lean body through the existing compiler.

For the two vocabulary kernels, reuse the existing transposed slices and
composition theorem, and prove their packed views correspond to the parent's
tied embedding in `vocabularyHead`. Parent embedding storage is vocabulary-
major. Our shader buffers are inner-dimension-major slices. This requires an
indexing/byte-view proof; matching shapes is insufficient.

Acceptance: the four biased product roles and both vocabulary roles have
checked output-word theorems against the actual parent definitions, plus
packed output-byte equalities. Test a small biased example and the six model
shapes on the CPU backend. First concrete deliverable: a compiled QKV kernel
and theorem equating its packed output to the parent's `linearRows` result.

## 3. Prove and execute one replacement matrix call

Use the parent's packed 4-byte word ABI throughout the new path. Keep
normalization, attention, activations, residuals, cache construction and
control arithmetic in Lean-generated Wasm. The GPU receives input words and
the selected packed matrix/bias view, then returns packed output words.

The replacement's contract must establish the parent's full postcondition:
correct bytes and length, output ownership, protected-input preservation,
disjoint output storage, allocation/free-list state, and completion before
the caller consumes the result. Review `LinearRows.Spec.linearRows_owned`
and `heap.PackedOutput` as the concrete contracts to match. Reuse the parent's
allocation and framing lemmas and the existing WGSL transfer lemmas where
their hypotheses fit the new packed ABI.

Implement and prove a minimal caller containing one QKV replacement before
rewriting the complete controller. Prefer a Wasm request/resume interface for
GPU dispatch so the same protocol supports native execution and asynchronous
browser WebGPU. Native C and browser JavaScript perform API calls, byte copies
and resume operations. Arithmetic and model-state decisions stay in Wasm/WGSL.

This is the principal integration risk. The parent's current call-region
proofs name a concrete module and function indices. Establish a reusable
call-contract/module-replacement lemma or generalize the affected call-region
proofs. Check the generated replacement caller and its ABI explicitly. Source
function equality alone does not prove a changed Wasm module.

Acceptance: a real native CPU dispatch satisfies the new caller protocol in
testing, and its modeled execution has the required packed-output/frame theorem.
The request/resume encoding, allocation behavior and browser-compatible API
must be settled by this milestone, before expanding to the entire model.

## 4. Compose the full hybrid token step and session

Apply the replacement boundary to the four products in each of twelve blocks
and the two vocabulary dispatches. Reuse the parent's block tensor decomposition,
cached hidden traversal and session induction. Generalize the relevant proofs
to the established call contracts; preserve the unchanged parent artifact
theorems as the reference case.

Derive new resource premises for the actual hybrid controller, including any
Wasm staging buffers and ownership transitions. GPU resources need their own
allocation/lifetime contract. Do not silently reuse the parent's memory budget
if the new controller allocates differently.

Acceptance: a checked hybrid cached-step theorem and an initialization-to-
128-position theorem return the parent's cache/logit trace under the declared
shader arithmetic interpretation and transfer/execution assumptions. Preserve
invalid-input behavior and prove releases as well as numeric results. No
unproved matrix-result premise may remain: discharge it with the compiled
shader certificates.

## 5. Validate the working model and deliver both runners

Start with the native CPU WebGPU path. Use identical forced token IDs and
checkpoint words for Wasm/WGSL comparisons, locating any first difference by
stage and token position. Run a compact stage corpus and boundary cases at
positions 0, 1, 126 and 127 while developing; run one complete 128-position
comparison after full composition. Check invalid inputs, cache reset,
allocation/release behavior and the context limit.

Run completions for the recorded story, science and France prompts, with
greedy selection first and a common Wasm sampler for sampled comparisons.
The parent's current CLI computes sampling probabilities in Python. Keep
sampling arithmetic in Wasm for this branch, consistent with the user's
requirement. Its current xorshift sampler and the parent's SplitMix64 sampler
produce different draws, so equal seed numbers alone are not a comparison
contract. Tokenization and sampling remain separately identified proof scopes.

Then run the same packed artifacts and request/resume protocol in the browser,
with JavaScript limited to host bindings. Test an actual browser completion
and stopping behavior. Record observed numerical differences explicitly.

The exact modeled theorem uses the stated FP32 operations and word-preserving
execution model. WebGPU may differ on fusion, subnormals, signed zero and NaNs;
Wasmtime's canonical-NaN switch does not configure WebGPU. Runtime tests
measure the selected backend's behavior. They do not prove universal driver
conformance. User-approved WGSL numerical differences remain permissible,
but they must not be reported as exact equality to the strict parent model.

Acceptance: working native and browser completions, reproducible source and
artifact checks, a documented hybrid theorem, and explicit runtime assumptions.
Keep generated shaders, Wasm, weights, proof fragments, binaries, reports and
archives out of new commits. Commit and push source/proof/documentation
increments at each completed milestone. Numerical bounds over the reals and
new exact-byte packaging work are outside this integration agenda.

## Status

- [x] Fetch and pin the parent revision.
- [x] Read the public step/session theorem, source operations and parent test record.
- [x] Preview the merge and identify conflicts and ABI/proof differences.
- [x] Merge and recheck both baselines.
- [x] Prove compiled biased products and vocabulary against the parent source.
- [ ] Prove and execute the packed replacement-call boundary.
- [ ] Compose hybrid cached-step and 128-position execution.
- [ ] Run native and browser completion evidence for the integrated model.
