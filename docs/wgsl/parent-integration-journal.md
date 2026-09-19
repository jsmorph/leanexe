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
