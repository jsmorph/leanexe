# Artifact correctness over floating-point words

The WGSL counterpart of “the generated module computes the Lean function” is
already available as `Project.WGSL.Binary32.Package.exact`. For the independently
parsed GEMM shader, valid buffers, a modeled execution, and the separate
binary32 profile, it proves

```text
output[row * cols + col] =
  gemmCell Binary32.arithmetic config A B row col
```

This is equality of 32-bit words. It has no real-valued reference or numerical
error premise. The package also supplies termination and memory-safety results.
Only the supported, selected Lean GEMM definition is generated as WGSL.

The profile fixes nearest/even rounding, preserved subnormals, IEEE zero signs,
source order, and separate multiplication and addition. A shader cannot itself
force a native runtime to obey those choices; runtime conformance is explicit.

## An independent algorithm specification

[`FloatSpec/Algorithm.lean`](../../proofs/talos/lean/Project/TinyGpt2/FloatSpec/Algorithm.lean)
specifies the four-position GPT algorithm over `UInt64` and `UInt32`. Typed
vectors and matrices describe parameters and intermediate values. The file
does not import the implementation's `Row`/`Context` types, packed weight
offsets, Wasm instructions, or a real-number model.

The specification fixes each choice that can affect the output bits:

- Binary64 dot products use balanced sums; the binary32 head uses four
  sequential updates starting at positive zero. Products are rounded before
  addition.
- Normalization fixes the mean, centered variance, epsilon word, square root,
  division, scale, and shift operations.
- Attention fixes the two heads, score scaling, causal mask, maximum selection,
  polynomial coefficient words, range reduction, and exponential cutoff.
- GELU fixes its polynomial/exponential arithmetic, signed branches, and tails.
- The head converts its four inputs and weights to binary32, computes the
  selected GEMM, promotes its result, and adds each bias in binary64.

`FloatSpec.logits:v1` names this algorithm. In particular, it includes the
rounding and cancellation of the current implementation. A rearrangement that
changes output bits is a change to the algorithm specification, even when it
represents the same real expression. This result does not repair the numerical
losses documented in the [earlier audit](numerical-audit.md).

[`Correspondence.hidden_eq`](../../proofs/talos/lean/Project/TinyGpt2/FloatSpec/Network.lean)
and [`Correspondence.logits_eq`](../../proofs/talos/lean/Project/TinyGpt2/FloatSpec/Head.lean)
prove universal equality between the existing Lean implementation and this
independent specification. These theorems are additional algorithm-level
assurance; they are not necessary merely to establish that a shader computes
the selected Lean GEMM function.

The executable reference uses
[`Evaluation.hidden`](../../proofs/talos/lean/Project/TinyGpt2/FloatSpec/Evaluation.lean)
to store finite intermediate vectors in arrays. `Evaluation.hidden_eq` proves
that this changes evaluation cost without changing any result word.

## Connecting the exact artifacts

[`GptFloatArtifact.artifact`](../../proofs/talos/lean/Project/WGSL/GptFloatArtifact.lean)
composes the existing hidden Wasm, dispatch bridge, parsed WGSL head, and finish
Wasm. Its staged conclusion establishes:

1. The hidden Wasm bytes decode and validate, execute successfully, preserve
   their input memory, and return `FloatSpec.hidden` in the prescribed ABI order.
2. The bridge terminates successfully. Every binary32 word read from its output
   memory equals `FloatSpec.headWord`.
3. The finish Wasm bytes decode and validate, execute successfully, preserve
   memory, and return the corresponding binary64 word of `FloatSpec.logits`.

The theorem quantifies over runtime parameter arrays of at least 2,488 words,
every context of four byte tokens, and every position 0–3. It has no parameter
magnitude bound and no real-valued reference or error tolerance. Memory layout,
input uploads, precision conversion, and host/runtime behavior are explicit
premises. The theorem composes stages through those premises; it does not prove
the JavaScript orchestrator implements them.

The pinned Wasm semantics use pure IEEE word operations, including a particular
canonical NaN. The precision conversion definitions have their IEEE meaning on
finite inputs. Their total word functions outside that domain are not a claim
about native NaN/infinity conversion. Consequently, the theorem's generic word
domain must not be mistaken for unconditional native bit equality on arbitrary
NaNs or infinities. Native execution must satisfy the stated word semantics,
including finite conversion inputs and the separate binary32 profile.

## Independent checking and CPU execution

From the configured repository root:

```sh
source tools/macos-env.sh # configured ARM Mac only
tools/artifact-proof.js wgsl-float-check test/wgsl/gpt
tools/artifact-proof.js wgsl-float-run test/wgsl/gpt 3 76 101 97 110
tools/artifact-proof.js wgsl-float-corpus build/wgsl/my-float-corpus
```

The corpus destination must be fresh. All Lean invocations use the repository
runner sequentially. The gate checks the actual shader and semantic manifest,
the bridge, and byte identity of the proved hidden and finish Wasm artifacts.
It generates and checks `checkedFloatExecution` for that exact shader package
and records the specification source hashes. Existing receipts cannot authorize
an execution. Proof audits accept only `propext`, `Classical.choice`, and
`Quot.sound`; neither `sorryAx` nor native decision axioms are accepted.

The reused shader/bridge gate still checks its existing numerical certificates
as well. They are not premises of the new GPT float-output theorem.

The executable harness accepts exactly 2,488 finite binary64 parameter words
with magnitude at most four, checked by comparing sign-cleared encodings with
`0x4010000000000000`. This is a test-harness domain, not a restriction on the
generic word theorem. Execution uses the existing server-side CPU WebGPU
runtime and compares hidden words, raw binary32 head words, and final binary64
logits against the checked reference. Comparisons use exact word equality.

The fixed corpus covers all four positions, three checkpoint contexts, and
both parameter arrays from the cancellation audit. Rejection cases alter the
hidden or finish Wasm, insert infinity as a parameter, or exceed the cap by one
representable word. Seven kernel-checked contract examples separately exercise
signed zero, subnormals, summation order, the exponential cutoff, and canonical
NaN arithmetic. Finite execution results are regression evidence, distinct
from the universal Lean theorems and from runtime conformance assumptions.

The retained [CPU corpus](../../test/wgsl/float-spec) passes all six executions:
24 hidden words, 1,536 raw head words, and 1,536 final logits match exactly.
All four invalid-input cases are rejected. No Wasm or WGSL bytes were changed
or regenerated for this specification work.
