# GPT2/128 CPU execution evidence

The [corpus](corpus.json) records seven successful mixed-precision executions
and four invalid token-domain checks. All 1,792 raw binary32 head words and
1,792 final binary64 logits match Lean. The additional
[128-byte text prompt](prompt.txt) has its own [execution](execution/input.json)
and [reference](reference/input.json), with another 256 exact comparisons at
each output stage. Its highest-scoring next byte is space (32).

The hidden computation executes directly in Lean. The [verification receipt](gpt128-verification.json)
establishes the exact bridge, WGSL projection and finish artifact contract,
conditional on the declared transfer/runtime premises. It explicitly does not
claim a complete hidden-Wasm proof or universal native runtime conformance.
The [scope and commands](../../../docs/wgsl/gpt128.md) describe that boundary.

The checkpoint is [the parent's 128-position model](../../../data/tiny-gpt2-128-v1/checkpoint.json).
Shader, manifest, bridge and finish bytes are shared with [../gpt](../gpt);
that directory's four-position hidden Wasm is not used. The portable receipt
and generated [head package proof](proofs/Gpt128PackageProof.lean) identify the
exact artifacts and selected model source files. Both verification attempts
produced identical receipts.

Execution reports, proof files and checker receipts are copied unchanged.
Reference JSON is compacted without changing any values, retaining prepared
weights, upload words, promoted words, mixed results and binary64 comparison
results. `corpus.json` only relocates its evidence references and adds the text
demonstration. Full diagnostics remain in the original build attempts
check-hTFGw7 and check-d7rBqu.

The largest observed difference from the parent's binary64 head across these
eight runs is approximately 1.071e-6. This is a finite-run observation, not a
uniform numerical theorem. Exact equality is checked against the mixed Lean
function.

Regenerate the corpus with:

```sh
tools/artifact-proof.js wgsl-gpt128-corpus build/wgsl/my-gpt128-corpus
```

The driver verifies current artifacts independently before execution; it does
not trust these retained receipts.
