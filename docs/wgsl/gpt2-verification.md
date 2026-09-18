# WGSL artifact fidelity for pretrained GPT-2

This branch's verification work concerns the WGSL computations and matrix
layouts. The specification is the selected Lean matrix-product algorithm
over floating-point words. Real-number accuracy bounds, a new GPT controller,
and general Wasm proof development are outside this workstream.

## Body-compiled shaders

New GPT-2 builds compile the six definitions in `LeanExe.WGSL.Gpt2` through
`#compile_wgsl`. Each definition calls `dense`; the compiler opens that helper,
reads its fold callback and translates its arithmetic and buffer indices.
The builder no longer invokes the fixed GEMM template generator. The generated
entry point is `lean_kernel`, selected by both the native and browser hosts.

Each compilation checks three theorems: the actual shader parses into the
recorded statement program, its source interpretation equals the named Lean
definition, and its execution returns that value at the correct address without
modeled errors. `Project.Gpt2.Matrix.from_body_shader` supplies a fourth
checked connection to the existing packed GPT-2 matrix product under concrete
binary32 arithmetic. All four dependency lists are audited. Generated shaders,
proof fragments and logs remain under ignored `build/`.

`wgsl-gpt2-check` recognizes the bundle's `shaderCompiler: lean-body-wgsl`
declaration and checks its six existing shader texts with `#check_wgsl`, then
checks their connection to the packed matrix specification. It also retains
the fifty-matrix routing-plan check. It replays the two vocabulary shader
certificates together and applies `vocabulary_from_body_shaders` to their
actual texts. This proves that `vocabularyBodyRun` selects the proper shader
and local column, shifts the right output address, and returns the Lean
vocabulary product for every token below 50,257. The receipt records this
separate composition theorem and its audited dependencies. It is a proof of
that declared composition, not of the native or browser host implementation.
Older bundles without that declaration
continue through the original template-artifact checker described below.

This new path uses the [body compiler's statement execution semantics](body-compiler.md),
including u32 indices, checked reads/stores, bounded loops and lexical scope.
Its arithmetic is source ordered and separate. It does not inherit the old
template path's fusion theorem or general interleaved-dispatch theorem merely
because the algorithms agree. Shared geometric theorems prove dispatch coverage
and disjoint output addresses. Runtime conformance and complete model/Wasm/host
composition remain outside these certificates.

## Original template-artifact verification record

The following sections describe the older bundle and its separately developed
proofs. They do not claim that its shader text was compiled from a Lean body.

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

`ArithmeticChoice.evaluate` is now an explicit Lean binary32 algorithm with
one Boolean choice per accumulation step: a fused multiply-add, or a multiply
followed by an add. `fusion_iff_choices` proves that its possible word results
are exactly the results admitted by the fusion profile. Choosing separate
operations throughout gives the original `columnAccum` function exactly.

`Matrix.fusion_from_dispatch` connects a parsed shader to that algorithm.
For each output word, there is a concrete choice sequence that produces exactly
that word. Different output invocations may use different sequences. The
vocabulary split preserves this correspondence too. The separate-profile
theorem and fusion theorem are checked independently for each shader; neither
asserts which policy a physical GPU selects.

The checker includes a two-term example with different exact answers: separate
operations give `0x00000000`; fused operations give `0xa8800000`. Both belong
to the modeled fusion profile, each through its explicit Lean computation.

General reassociation and other subnormal/exceptional-value policies remain
outside these v1 profiles. Extending those policies would require additional
Lean semantics and proofs. No result here is an error-bound theorem or a claim
of conformance by an arbitrary browser GPU.

Connecting certificates to runtime file loading was removed from the agenda
at the user's request. Work remains focused on the computations, layouts, and
explicit arithmetic semantics. Complete GPT-2/Wasm composition remains a
separate workstream.
