# WGSL artifact fidelity for pretrained GPT-2

This branch's verification work concerns the WGSL computations and matrix
layouts. The specification is the selected Lean matrix-product algorithm
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

## 2. Connect the products and matrix decomposition

`Project.Gpt2.Matrix.product` specifies the six dense products as source-ordered
binary32 dot products. `MatrixView.packed_at` proves the row-major indexing
formula, and `MatrixView.from_dispatch` connects the checked shader execution
to those matrix coordinates. Every shader certificate now specializes this
connection to its named GPT-2 role and proves exact output words under the
separate profile.

`vocabulary_from_dispatch` proves that joining the 25,129-column and
25,128-column outputs computes all 50,257 vocabulary products against the
transposed token embedding. The proof preserves the complete order of each
dot product, including permitted fusion choices. `vocabulary_exact` specializes
this to exact output-word equality with the Lean vocabulary function. There is
no reassociation of additions and no numerical approximation in this split.

`layer_shape`, `layer_matrix_injective`, `head_shapes`, and `fifty_matrices`
prove the four-per-layer numbering, absence of overlapping layer assignments,
and coverage of all fifty matrix slots. The checker compares the demo's fifty
matrix descriptors with this Lean plan. The attention input slice is also
defined and its range proved: words 1,536 through 2,303 of the attention result.

The inputs here are the binary32 words presented to WGSL; the outputs are the
binary32 words before conversion back to binary64. The proofs quantify over
arbitrary matrix words. They do not establish checkpoint provenance, correctness
of the Python packer or C/JavaScript controller, or the Wasm float conversions.
The descriptor comparison checks matrix routing metadata, not matrix contents.

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

Connecting certificates to runtime file loading was removed from the agenda
at the user's request. Work remains focused on the computations, layouts, and
explicit arithmetic semantics. Complete GPT-2/Wasm composition remains a
separate workstream.
