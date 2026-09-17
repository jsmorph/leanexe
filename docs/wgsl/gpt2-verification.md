# WGSL artifact fidelity for pretrained GPT-2

This branch's verification work concerns the WGSL artifacts and their GPU-call
interface. The specification is the selected Lean matrix-product algorithm
over floating-point words. Real-number accuracy bounds, a new GPT controller,
and general Wasm proof development are outside this workstream.

## 1. Check the six delivered shaders

```sh
source tools/macos-env.sh # configured ARM Mac only
tools/artifact-proof.js wgsl-gpt2-check build/gpt2/bundle
```

The checker holds the six existing shader files, checks their identity against
the demo manifest, and independently parses and proves each shader. It does
not regenerate replacement kernels. The dimensions are:

| Product | Rows | Columns | Inner dimension |
| --- | ---: | ---: | ---: |
| QKV projection | 1 | 2304 | 768 |
| Attention projection | 1 | 768 | 768 |
| MLP expansion | 1 | 3072 | 768 |
| MLP projection | 1 | 768 | 3072 |
| Vocabulary projection, first half | 1 | 25129 | 768 |
| Vocabulary projection, second half | 1 | 25128 | 768 |

Each theorem connects the parsed artifact to `gemmCell Binary32.arithmetic`:
separate binary32 multiplication and addition in the specified source order,
starting from positive zero. It quantifies over correctly sized input buffers;
there is no parameter-magnitude condition or numerical error tolerance.
The formal arithmetic specifies subnormals, signed zero, and exceptional words.
Termination, indexing safety, dispatch coverage, and non-conflicting output
writes come from the generic dispatch proof.

`Project.WGSL.ExecutionPackage` contains this word-level proof path separately
from the optional numerical certificates. `wgsl-word-check` applies it to any
supported shader package. The legacy checker remains available.

The source/parser result, configuration, semantic manifest, and proof axioms
are checked afresh. Generated proofs and receipts stay under ignored `build/`.
Receipts are evidence records, not authority for a later unchecked execution.

All six delivered shaders passed this check on 2026-09-17. The independently
checked package, dispatch artifact, and equality theorem use only `propext`,
`Classical.choice`, and `Quot.sound`; none uses `sorryAx` or a native-computation
axiom. This completes the first stage under the stated arithmetic profile.

## 2. Prove the GPU-call interface and matrix decomposition

Connect these six kernel results to named Lean matrix operations at each call
site. Prove the row-major packed layouts and input/output slices, and prove
that joining the two vocabulary outputs is the full Lean vocabulary product.
State resident-buffer immutability, input snapshots, completed dispatch, and
readback as an explicit host interface. Check the actual fifty weight-buffer
assignments against that interface. This does not require rewriting or proving
the complete model controller on this branch.

## 3. Make the arithmetic profile explicit

The first theorem uses `leanexe-f32-rne-separate-v1`. It proves exact word
equality under that profile. It does not establish that a browser GPU follows
the profile. The existing fusion profile permits a separate or fused update
at each accumulation step; it does not cover general reassociation, alternate
subnormal policies, or all WebGPU exceptional-value behavior.

For broader browser support, define the supported choices in Lean and prove
that each modeled shader execution is an execution admitted by the Lean
algorithm. Fixing those choices gives an exact result; allowing several gives
a relation over permitted word results. Neither result is an error-bound
theorem. Do not infer runtime conformance from one successful model completion.

## 4. Bind checking to execution

Connect the word-level checker to the native/browser launch path so the shader
text and dispatch metadata used by execution are the held, checked inputs.
Keep driver/compiler conformance separate from artifact correctness. Focused
bit-pattern tests should exercise rounding, fusion, subnormals, indexing, and
rejection of changed artifacts. They are regression evidence for the remaining
runtime assumptions, not a substitute for the Lean proofs.

The first deliverable is complete: six shader certificates. Later deliverables cover
their GPU-call interfaces and a precisely stated browser arithmetic contract.
Complete GPT-2/Wasm composition remains a separate workstream.
