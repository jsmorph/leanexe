# Parent FP32 integration journal

## Parent merge and baseline, 2026-09-18

The approved parent revision is `f4d412b709a13bb2649fe23be267ec9928838064`.
The three merge conflicts preserve both packing proof developments (the older
WGSL numerical lemmas now use `F32PackingBounds`), retain the completed parent
plan, and provide explicit `tools/gpt2-wasm` and `tools/gpt2-wgsl` launchers.
The compatibility command routes `build/run/serve/test` to the existing WGSL
demo and plain flags to the parent's Wasm CLI. Its Python sampler remains a
reference implementation, not the integrated runner's intended sampler.

The first parent gate rebuilt the compiler and exact generated artifact, then
timed out at the proof build's 15-minute limit. The last completed target was
`Project.Gpt2CachedStep.CachedBlock.CacheSize`; arithmetic, allocator, memory,
linearRows ownership, LayerNorm and most attention dependencies had passed.
There was no Lean proof error or `sorryAx` in the log. This is a failed gate,
not a completed baseline. Evidence: `build/gpt2/parent-merge-proof.log`.

The remaining dependency build was divided into `CachedBlock.Spec` and
`Session.Spec` before another gate invocation. This avoids repeating the
unchanged cold build after timeout. The new packed shader/source/view proofs
were drafted independently while the baseline held the sequential Lean lock;
their checks are still pending.

Both staged targets passed: the block build completed 3,630 jobs and the
session build 3,691 jobs (including cached dependencies). The repeated parent
gate then passed 3,694 jobs, including `cachedStep_exact` and `gpt2_128_exact`.
Logs are `parent-merge-block.log`, `parent-merge-session.log`, and
`parent-merge-proof-final.log` under `build/gpt2/`. The two renamed packing
consumers passed in `parent-merge-packing.log`. The WGSL body corpus passed:
11 proof triples, 63 exact CPU words, 24 rejected negative cases, and two body
mutation comparisons (`build/wgsl/body-check-J7lQmq/summary.json`). All six
installed shader certificates and their vocabulary composition passed in
`build/gpt2/shader-checks/check-ENZDAO/verification.json`. This completes the
merged baseline, before changing the model's execution path.

## Actual 124M execution comparison

The user requested full model executions, not only component checks. A fresh
native CPU run of the existing mixed-precision WGSL bundle generated sixteen
greedy tokens after `The capital of France is`. The rebuilt, proved parent
cached-step Wasm artifact was run on the identical contexts, and PyTorch ran
the same checkpoint and token sequence. Both checkpoint and packed-weight
hashes match the parent's recorded values. The reference uses already-installed
PyTorch 2.9.1 and Transformers 4.57.1; the parent's lockfile pins Transformers
4.57.6, so this local reference is not presented as that locked environment.

All three implementations chose the same sixteen tokens. Each candidate was
compared with 804,112 PyTorch logits. Maximum absolute errors were
0.00016021728515625 for the parent and the existing WGSL bundle; the maximum
between the two artifact implementations was 0.0001678466796875. The parent
session retained only weights and cache, with 5,161 allocations and 5,159
releases, and used 514,129,920 bytes of Wasm memory. The evidence is
`build/gpt2/parent-comparison/france.json` and its retained traces/logs.

The text is repetitive in all three: `The capital of France is the capital of
the French Republic, and the capital of the French Republic is the`. Matching
that output establishes agreement for this test, not general language quality.
This test covers the existing WGSL bundle and the new parent baseline. It does
not establish execution of the newly drafted packed FP32 hybrid implementation.

The same comparison then passed for `The purpose of science is` (24 generated
tokens) and `Once upon a time, in a small village,` (16 generated tokens).
Across all three prompts, all three implementations agreed on all 56 greedy
tokens and compared 2,814,392 logits per implementation. Maximum absolute
differences were 0.00032806396484375 (parent versus PyTorch),
0.000213623046875 (existing WGSL versus PyTorch), and 0.000244140625
(WGSL versus parent). Every tested logit was finite and passed the declared
`0.002 + 0.0001 * abs(reference)` tolerance. Evidence is `science.json` and
`story.json` alongside the France report. The science completion was:

> The purpose of science is to understand the world around us, and to understand how we live and what we do.
>
> The science of the

`tools/wgsl/gpt2/compare-parent.py` makes this comparison repeatable using a
fresh native WGSL trace, the parent artifact, and the same checkpoint. It
records versions, per-position errors, selected tokens and allocator state.

## Packed FP32 shader/source connection

`Gpt2Packed` defines the four supported biased kernels, with the FP32 bias
addition after the ascending dot product. `PackedBody` proves the source
arithmetic connection for all words, the reduction order, contiguous matrix
and bias views, transposed vocabulary views, and exact packed output equality
to the parent's `linearRows` and `vocabularyHead`. `PackedShader` applies the
body compiler's parsed-statement execution certificates to those equalities.
There is no magnitude bound or real-number approximation.

The first proof build failed at an unfolded recursion rewrite and an
over-eager congruence tactic on the large vocabulary generator. Keeping the
recursive fold explicit and using bounded generator extensionality fixed both;
the second build passed. Logs: `build/gpt2/packed-proof-01.log` and `-02.log`.
All printed public theorem dependencies are the standard Lean axioms, without
`sorryAx`. The six concrete shader certificates and packed parent connections
passed in `build/gpt2/packed-parent-01/results.json`.

The first small runtime-test declaration omitted explicit entry parameters,
which the documented body compiler rejects. Its retained diagnostic is
`packed-parent-01/small.log`. After adding the five explicit parameters, the
small biased kernel and all six full model shapes passed on SwiftShader CPU:
57,171 output words matched the original Lean definitions exactly. The input
`[2^24, -2^24, 1, 0, ...]` with unit matrix/bias detects incorrectly placing
bias before the dot product. Expected words are evaluated in Lean, not in the
host harness. Evidence: `packed-parent-01/execution.json` and
`build/gpt2/packed-parent-test-02.log`.

Repeat with `node tools/wgsl/gpt2/packed-shaders.js FRESH_DIRECTORY --test`
after sourcing the platform environment. `--test-existing` resumes only the
runtime-test stage after a successful six-shader proof receipt. The complete
hybrid Wasm caller/session theorem and universal WebGPU conformance remain
outside this milestone.

## Experimental full packed execution

`packed-module.js` creates a separate experimental artifact from the parent
WAT. It retains the parent's non-matrix function bodies, renames direct call
and export indices for two new imports, and replaces only the linear-product
and vocabulary bodies. The replacement functions call the existing Wasm
allocator, invoke WebGPU, then return the packed pointer/length triple.
The host performs GPU API calls, layout copies and synchronized readback.
No non-matrix FP32 computation moves into C, JavaScript or Python.

This selects a synchronous Wasm import as the call boundary. Native execution
waits for readback before returning. A browser worker can suspend at the same
boundary using a shared-memory request/completion exchange; that browser path
is not implemented yet. The parent cached-step proof does not automatically
apply to this transformed module. The separate wrapper and full-module proof
obligations remain pending, and this artifact is labeled experimental.

The 124M packed artifact passed three common-context comparisons with both
the original parent artifact and PyTorch: France, science and story, sixteen
predictions each. All 48 greedy argmax choices agreed, and all 2,412,336 logit
words were bit-identical between the packed hybrid and parent Wasm. The maximum
absolute difference from PyTorch was 0.00032806396484375. Both artifacts had
identical allocation/release counts and memory size on each prompt; only the
weights and current cache remained live. Reports and logs are under
`build/gpt2/packed-runtime-01/`. The reference test chooses forced tokens in
Python; this is a test harness, not the delivered sampler.

Reproduction, with an existing pinned checkpoint and parent artifact:

```sh
source tools/macos-env.sh
node tools/wgsl/gpt2/packed-module.js proofs/talos/.generated/gpt2_cached_step/program.wat build/gpt2/FRESH_RUNTIME
sh tools/wgsl/gpt2/compile-packed-host.sh
export LEANEXE_PACKED_SHADERS="$PWD/build/gpt2/packed-parent-01"
build/gpt128-quality/venv/bin/python tools/wgsl/gpt2/compare-packed.py \
  --candidate-host tools/wgsl/gpt2/packed-cpu.sh \
  --candidate-wasm build/gpt2/FRESH_RUNTIME/model.wasm \
  --prompt 'The purpose of science is' --generate 16 \
  --output build/gpt2/FRESH_RUNTIME/science.json
```

The shader directory is the output of the preceding certificate gate; use
its actual path when generating a fresh set. The existing generic Wasmtime
host remains the parent comparison host. The packed host is a separate build.

## Concrete QKV wrapper proof

`PackedCall` proves allocation plus completed shader-byte transfer gives the
parent's `Heap.PackedOutput` contract, including ownership, heap/frame state,
pages and memory capacity. It also proves that the full write frame and
represented bytes uniquely determine the final store. These are transfer
lemmas, not by themselves Wasm execution theorems.

`PackedWrapper.qkv_exact` additionally proves execution of the real linear
wrapper instruction sequence for QKV: Wasm allocation, the completed host
call, and the returned owner/pointer/length triple. The explicit host premise
says the import completes the modeled shader execution and copies its bytes
without other store changes. The certificate, rather than a parent-output
assumption, supplies the matrix's numeric equality. This leaves actual host
and driver conformance as an external execution assumption.

Three proof iterations corrected transparent-name and list-normalization
mismatches in the Wasm stack/frame proof. The fourth passed without additional
axioms (`build/gpt2/packed-wrapper-01.log` through `-04.log`). The independent
`packed-check.js` driver parsed the actual hybrid Wasm using Talos, checked
its wrapper and allocator declarations against the proved functions, replayed
the concrete QKV shader certificate, and applied the wrapper theorem.
Evidence: `build/gpt2/packed-wrapper-check-01/results.json`. This checks the
replacement QKV call; it does not yet prove the complete hybrid token/session.

A separate one-prediction rerun after adding GPU cleanup also passed, with
250 actual shader dispatches for five prompt tokens and zero differing
parent logit words (`packed-runtime-01/cleanup.json` and `.log`).

## Native prompt runner with Wasm sampling

`tools/gpt2-packed` now runs the experimental packed model on a prompt.
`packed-cli.h` invokes the parent hybrid Wasm for every token, the existing
Lean-generated tokenizer for BPE/decoding, and the existing Wasm sampler.
FP32-to-FP64 conversion for that sampler is performed by `transfer.wasm`.
The C host performs no floating-point model or sampling arithmetic. It releases
each old cache and each logits allocation and stops at EOS, the requested
generation count, or rejects a request exceeding the context before inference.

The assembled local bundle is `build/gpt2/packed-bundle`; it includes references
to the existing checkpoint and generated tokenizer/sampler artifacts. Assemble
a fresh bundle with `prepare-packed.js RUNTIME CHECKED_SHADERS FRESH_BUNDLE`.
This is an assembly command, not a full clean source rebuild or proof gate.
The source rebuild/verification entry point and browser delivery remain pending.

The actual native CLI produced the sixteen-token science completion, executing
1,000 GPU dispatches. Its f32 logit trace passed `compare-parent.py --trace-float
f32`: all 804,112 words were bit-identical to the parent, and all greedy token
choices agreed with both parent and PyTorch. Evidence is
`packed-runtime-01/native-science.f32.bin`, `native-science.txt`, and
`native-science-compare.json`. Run locally with:

```sh
tools/gpt2-packed --prompt 'The purpose of science is' --generate 16 --temperature 0
```

The prompt runner reports that the full hybrid session proof is pending.

## Reusing unchanged Wasm function proofs

`FunctionRegion.ImportShift` permits host imports outside a closed region of
Wasm-defined functions. Its checked execution theorem transports the same
store/return behavior after renaming calls, and its total-correctness theorem
transports `TerminatesWith` specifications. Memory declarations must match;
every called function must remain in the closed region. It does not assume
matrix-call equivalence or permit the region to call an unchecked import.

Applied to the independently parsed hybrid artifact, this passed for all 38
unchanged functions outside the two matrix replacements and three controllers
(original indices 21, 33, 36, 37 and 38 are excluded). This covers the retained
arithmetic operations, normalization, attention, activations, residuals, layout,
allocation and release functions. The controller proofs remain to be composed
using the replacement-call contracts. The first generated proof used an
unavailable tactic and failed; explicit constructor proofs and normalized
membership cases passed in `build/gpt2/packed-region-check-02/results.json`.
The generic theorem build is recorded in `build/gpt2/region-imports-01.log`.

## All matrix wrapper contracts

`PackedLinear.exact` generalizes the QKV instruction proof to any certified
one-row biased product whose output byte count fits the 32-bit memory bound.
It preserves the actual allocator's rounded capacity and the returned byte
length. `PackedVocabulary.exact` checks the second wrapper, composing both
shader halves and distinguishing the 201,028-byte result from its 201,032-byte
allocation capacity. All public dependencies are the standard Lean axioms.
The generic linear proof required explicitly normalizing the call frame before
rewriting its byte-count multiplication; the retained failed/successful logs
are `packed-linear-01.log`, `packed-calls-02.log`, and `packed-linear-03.log`.

The expanded `packed-check.js` independently parses the hybrid Wasm and applies
these contracts to all four concrete biased shaders and both vocabulary halves.
All five operation checks passed in `build/gpt2/packed-wrapper-check-02/`.
Each check discharges its shader certificate premise using the generated
certificate, and leaves the completed host execution/transfer assumption
explicit. The full controller/session proof is still pending.

## Actual matrix offsets and host cache invalidation

The native host now constructs matrix/bias views from the offsets supplied by
Wasm instead of duplicating GPT-2 block-layout constants. It copies raw words,
including separately located biases and the two transposed vocabulary slices.
The sixteen-token native science trace remained byte-identical to the earlier
trace (`packed-runtime-01/views-science.f32.bin`).

Cached GPU views are invalidated on a Wasm reset or an external host write to
their source weight array. The focused `packed-host-test.js` exercises the
actual QKV wrapper at noncontiguous offsets, changes a bias through the host,
then resets and reallocates the input. All three calls returned the expected
6,912 FP32 words exactly (`packed-host-test-01/results.json`). Expected words
come from the existing Lean fixture. The host supports at most 64 concurrent
cached views; the full model uses 50. Successful GPU allocation and execution
remain explicit runtime assumptions rather than Lean-proved properties of C
or of the driver.

## Controller-facing replacement contracts

`PackedBackend.linear_owned` now exposes the parent's complete linear-call
postcondition: exact bytes and returned length, owned output, heap state,
protected-memory frame, page bound and memory-capacity preservation. The
vocabulary bridge supplies the corresponding packed-output contract. The
interfaces distinguish checked shader semantics, actual module declarations,
and the external assumption that a host invocation finishes the declared
shader execution and copies only its output bytes. They do not assume that
the matrix result equals the parent: that equality follows from the compiled
shader certificates and packed-source theorems.

These bridges passed in `packed-backend-04.log`, with only the standard Lean
axioms. The retained earlier logs include a missing size-lemma import and a
normalization mismatch in the vocabulary bridge. The full controller proof
is being replayed against the independently parsed hybrid module in a separate
generated namespace; it is not yet established by these bridge lemmas.

## Complete hybrid transformer block

The proof preparation tool `packed-compose.js` reuses parent controller proof
text in a separate generated module, adjusts direct function indices for the
two imports, and checks the resulting declarations with Lean. Each controller
segment still proves its literal instruction sequence matches the independently
parsed hybrid Wasm. Unchanged helper contracts are transported through the
proved closed call region; the four matrix call contracts use the concrete
compiled shader certificates. The proof generation text transformations are
not trusted: a wrong index, instruction sequence, or postcondition is rejected
by the generated Lean checks.

The QKV controller passed in `packed-compose-02/logs/run-3.json`. The complete
block then passed in `run-5.json`, including all products, attention, residuals,
cache construction, allocation and cleanup. Its public theorem is
`Project.Gpt2Hybrid.CachedBlock.Spec.cachedBlock_exact`, conditional on the
explicit host execution/transfer interface. All audited dependencies are the
standard Lean axioms. The failed attempts are retained: generated import-root
resolution, theorem headers containing `let`, role-size normalization, and a
packed-word helper whose old API required an import-free module. That helper
was handled by the existing semantic transport theorem, preserving its original
proof instead of weakening the import premise.

The twelve-block traversal and complete token/session theorem remain pending.

## Sampled completion and independent packed assets

A paired native test used the same Wasm tokenizer and sampler with both the
unchanged parent module and the hybrid module. Temperature 0.8, seed 42 and
sixteen requested tokens produced byte-identical token/logit traces and text:
`Once upon a time, in a small village, the city seemed a lot like a city, like a city with a lot of`.
The hybrid run performed 1,250 shader dispatches with 50 weight views. Evidence
is `packed-runtime-01/{parent,hybrid}-sampled.{txt,log,f32.bin}`. Both trace and
text comparisons passed. This tests the actual delivered Wasm sampler path;
it does not add a sampler theorem.

`packed-assets.py` now creates the parent's packed weight layout and tokenizer
table directly from the pinned checkpoint. The table encoder is shared with
the earlier demo packer. Its 497,759,232 weight bytes and 1,747,605 tokenizer
words were byte-identical to the previously executed artifacts. Evidence is
`packed-assets-01/` and `packed-assets-01.log`. This is offline data preparation;
inference and tokenization remain in Wasm/WGSL. The source build gate is being
assembled separately and has not yet passed end to end.

## Full hybrid controller and 128-token session

The twelve-block traversal passed in `packed-compose-02/logs/run-6.json`.
The complete cached-step and initialization-to-session proofs then passed in
`run-9.json`. The public declarations are
`Project.Gpt2Hybrid.Spec.cachedStep_exact`, `gpt2_128_exact`, and
`gpt2_128_exact_for`. Their axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The proof includes rejected inputs,
embedding, all twelve blocks, final normalization, both vocabulary halves,
cache/logit ownership, initialization, allocation budgets and releases.
The vocabulary-call replay needed an explicit normalization of the rounded
201,032-byte capacity; failed logs 7 and 8 remain alongside the successful run.

The host premise is explicit: completed execution of the six certified shaders
under the declared separate FP32 semantics, exact output-byte transfer, and
preservation of other store fields. Matrix equality to the parent algorithm is
proved from the concrete shader certificates. This does not prove C, JavaScript,
WebGPU driver conformance, GPU allocation success, tokenizer correctness or
sampling correctness. The imported shader/module declarations are independently
prepared from the generated artifacts; the external binary parser/emitter is
still a translation trust boundary, as agreed for this integration.

The host reuses 50 GPU weight views during GPT-2 execution. The Wasm controller
allocates the same packed outputs as the parent, so the checked resource
derivation carries through without adding Wasm staging allocations. Browser
staging is in a separate shared buffer. Its implementation and actual browser
execution remain to be tested; the browser-control tool reported the Mac locked
and unable to unlock, and a user unlock request is pending.

A concurrent-parent check found `origin/main` at `d8777fcd`. Its algorithm and
controller were unchanged; new work concerned binary certificates and session
API generalization. Commit `ea73d3c6` was selectively incorporated as `1cd17438`
and the updated parent session theorem rechecked. The other parent binary and
publication artifacts were not imported. The hybrid session replay uses that
new module-parameterized API with the two imported-function indices accounted
for explicitly.

## Full 128-position execution comparison

`packed-session-test.py` executed the complete 124M checkpoint through the
hybrid and parent artifacts at every context length from one through 128.
All 6,432,896 FP32 logit words matched the parent bit for bit. All 128 argmax
choices agreed with PyTorch; the maximum absolute PyTorch difference was
0.0015411376953125, within the recorded `0.002 + 0.0001*abs(reference)` test
tolerance. No analytical error-bound claim is made by this measurement.

The complete cache byte arrays matched at positions 0, 1, 126 and 127. Both
artifacts rejected four invalid-input cases without changing allocator
statistics or memory size. Cache restart/replay was exact. Allocator statistics
and Wasm memory size matched at every position; at the last position both had
33,025 allocations and 33,023 frees, retaining only weights and cache, and used
1,107,361,792 Wasm bytes. The test, including both implementations and reference
comparison, took 113.98 seconds. The hybrid host logged 6,500 CPU WebGPU
dispatches, including the two restart calls, with 50 weight views.

Evidence: `packed-runtime-01/session128.json` and `.log`. The candidate Wasm
SHA-256 is `e509900d8497c8a498ff454bfbe728b1509928cf25f9837132925c7601b6761c`;
the parent remains `e93de126e00d7f5c5b9b30ca014a13b1385e9f91e3cb6b4e56a4aacf7a2b4ade`.
All generated reports, model binaries, shaders and checkpoint bytes remain
outside new source commits.

## Rebuilt source bundle and delivery status

The complete source gate passed in `packed-build-01/build.json`. It rebuilt
the parent artifact, prepared the hybrid module, compiled and checked all six
shaders, independently parsed the hybrid Wasm, checked all wrapper contracts,
and replayed the controller/session gate. The latter reused matching checked
proof objects from the development cache and audited the required public
theorems in `packed-compose-02/logs/run-10.json`. It then rebuilt the tokenizer,
sampler, conversion adapter and native C host. The model, conversion module,
weights and tokenizer table were byte-identical to the previously executed
versions. The tokenizer and sampler Wasm binaries changed under the merged
compiler, so they received focused execution checks.

The new bundle's sixteen-token science trace was byte-identical to the earlier
native trace. Its temperature-0.8 story trace was also byte-identical to the
earlier paired sampled test. Eight tokenizer cases, including whitespace,
contractions, combining characters, Chinese, Greek and emoji, matched the local
Transformers tokenizer and decoded to the original UTF-8 bytes. A known-logit
fixture selected EOS 50256 in the rebuilt Wasm sampler. Four invalid native
requests were rejected. These are runtime checks of auxiliary artifacts, not
new semantic proofs of tokenization or sampling. Evidence is
`packed-build-01/{science,sampled}.{txt,log,f32.bin}` and `aux-test/results.json`.

`tools/gpt2-packed build FRESH_DIRECTORY` is the source build entry point;
`tools/gpt2-packed --prompt TEXT` uses the most recently selected checked bundle,
and `serve PORT` starts its browser page. The browser source uses a Wasm worker,
shared staging and completion notification around the same two imports.
JavaScript performs host operations and raw-word movement only. Syntax checks
and localhost HTTP isolation headers passed. A headless Chrome launch aborted
during macOS application registration, and the browser-control tool then
reported the Mac locked and unable to unlock. The unlock request is pending;
no browser completion or browser numerical comparison has been reported as
passing. The temporary validation server was stopped.

### 2026-09-19 — CPU-only browser backend and comparison measurements

The packed browser host now accepts either the hybrid WGSL module or the
unchanged parent CPU Wasm module. The source build includes that parent as
`model-cpu.wasm`; the existing checked local bundle was extended with a byte
copy of the already checked parent artifact. No model/shader/proof was changed.
The CPU branch does not request a WebGPU device, load shaders, send weight
views, or allocate shared staging. Both branches use the same worker loop,
checkpoint, Wasm tokenizer, sampler and conversion adapter.

The page retains both completions and reports setup, prefill, decode, first-token,
sampling, text-decoding and total timings, plus explicitly scoped memory figures.
Compare both runs the backends sequentially with identical prompt/settings.
Decode throughput counts model calls after prefill, not the first token selected
from the final prompt logits. Wasm capacity and GPU buffer sizes are distinct
from physical process memory. The old `tools/gpt2 serve` / `tools/gpt2-wgsl serve`
entry now serves this packed comparison page on port 8766.

`packed-browser-test.mjs` exercised the actual browser host and worker under
Node worker bindings with WebGPU and SharedArrayBuffer unavailable. The science
prompt produced the same 16 token choices and all 804,112 FP32 logit words as
`packed-build-01/science.f32.bin`, with zero shader dispatches. Counter consistency,
monotonic memory observations, and cancellation before startup/during loading
passed. Evidence: `build/gpt2/packed-browser-compare-02/result.json`. This is
worker execution evidence, not browser/WebGPU evidence. The initial test adapter
had a missing closure; that test-only syntax error was fixed before the passing
run. No Lean proof rerun was needed for these host/UI-only changes.
