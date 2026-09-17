# Float specification evidence

This records the successful `wgsl-float-corpus` run on 2026-09-17. It uses the
unchanged artifacts in [../gpt](../gpt) and the independent
[`FloatSpec.logits:v1`](../../../proofs/talos/lean/Project/TinyGpt2/FloatSpec/Algorithm.lean)
algorithm. [The contract documentation](../../../docs/wgsl/float-specification.md)
states the theorem, domains, and runtime assumptions.

The [corpus receipt](corpus.json) indexes six CPU executions and their Lean
references: 24 hidden words, 1,536 raw binary32 head words, and 1,536 final
binary64 logits all match exactly. Four rejection logs identify changed hidden
or finish bytes, an infinity parameter, and a parameter one representable word
above four. These executions are regression evidence, not proofs of universal
native-runtime conformance.

The [float verification receipt](float-verification.json) records the exact
artifact and specification-source hashes and standard-logical-axiom audits.
The generated [package proof](proofs/FloatPackageProof.lean) binds the checked
shader to `GptFloatArtifact.artifact`. The base shader/bridge receipts and proof
sources are retained too. Receipt hashes are unchanged from the checker; proof
files are stored in `proofs/`, and artifact files are shared with `../gpt`.

The two adversarial parameter files are retained in `weights/`. They reproduce
`adversarial(1)` and `adversarial(-1)` from `tools/wgsl/audit/cases.js`.
Checkpoint runs use `../gpt/weights.bin`. All three parameter identities appear
in the execution reports. The generic float theorem accepts runtime parameters;
its correctness does not depend on a frozen checkpoint identity.

From the configured repository root, regenerate all checks in a fresh directory:

```sh
tools/artifact-proof.js wgsl-float-corpus build/wgsl/my-float-corpus
```

The driver independently verifies current files before execution; it does not
trust these retained receipts. The portable copy only relocates evidence paths
in `corpus.json`; execution reports, references, proof files and checker receipts
are copied unchanged. Runtime paths in those reports identify the observed
machine configuration and are not needed to interpret the word comparisons.
