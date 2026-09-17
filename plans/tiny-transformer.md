# Verified tiny transformer inference

This plan expands phase 14 of the [Development Plan](../plan.md).
The user authorized implementation, frequent commits and pushes, and
command-line demonstrations on 2026-09-16.  The first target is standard
exponential softmax.  The transported proposal informed this plan.

## Scope and proof boundary

Use the existing binary64 compiler and Talos semantics.  A completed component
includes caller-supplied command-line input, a WASM artifact, exact
generated-WAT agreement with its Lean source, termination throughout its
advertised domain, and memory guarantees.  The user deferred further
real-arithmetic error bounds on 2026-09-17.  Record the binary digest and the
theorem subject.  Exact-byte packages are deferred to later releases, as
authorized by the user.  The host input decoder and decimal display remain
outside the numerical theorem.  Hexadecimal words preserve the canonical input.

The first model has four byte-token positions, one pre-normalized block,
two attention heads of width two, model width four, and feed-forward width
eight.  Audit parameter layout, biases, LayerNorm epsilon, and evaluation
order before model integration.  The pinned TorchLean activation uses the
tanh GELU formula.  Training is outside the inference proof.

The user selected a proved 128-byte context as the subsequent target,
replacing the earlier 64-byte target.
The training backend remains CPU PyTorch 2.9.1 in the repository-local
environment.  The user approved the pinned Tiny Shakespeare corpus,
all byte tokens, and all 256 next-token logits per inference call.
The four-byte model's exact source-equivalence theorem is complete.
Parameterize new traversal proofs by length where practical.  The larger
model requires array-based context traversal, expanded positional embeddings,
training, and a checked proof for its compiled output.  Each proof must name
the original Lean source function and the generated module.

The user also authorized later seed-controlled sampling from the top k logits
using the [Lean PRNG](../docs/prng.md).  PRNG correctness remains outside the
formal proof scope.

The user subsequently approved runtime weight validation and clipping,
with a parameterized magnitude bound targeting [0, 10].  Nonfinite weights
are rejected.  Numerical guarantees refer to the clipped weights and must
reuse one theorem when the checkpoint changes.  The
[runtime-weight analysis](tiny-model-runtime-weights.md) records the
revised proof sequence, cancellation test, and numerical-method proposal.

## Completed numerical development

The following domains record the earlier numerical work.  Further error-bound
research is deferred.  Existing arithmetic definitions and execution proofs
remain reusable in the 128-position source-equivalence proof.

| Component | Initial domain | Required result |
|-----------|----------------|-----------------|
| Existing Horner baseline | Four binary64 magnitudes at most one half | Reproduced execution and error theorem. |
| Small exponential | Binary64 values in [-1, 0] | Finite positive output, exact one at zero, absolute error at most 1/4000 (proved). |
| Extended exponential | Binary64 values in [-8, 0] | Proved positivity and absolute error at most 1/300000 after range reduction and reconstruction. |
| Softmax | One to four scores in [-4, 4], nonempty prefix mask | Proved exact masked zeros, positive finite active outputs, component error at most 1/50000, and normalization error at most 32 times 2^-52. |
| LayerNorm | Four inputs, four scales, and four biases in [-4, 4] | Proved successful execution, absolute error at most 1/1000000, and input and parameter perturbation bounds, including constant inputs. |
| GELU | Finite binary64 inputs in [-3, 3] | Proved finite output, error at most 1/80000, and input perturbation multiplier four. |
| Affine operations | Explicit bounded inputs and parameters | Local error and perturbed-input bounds. |
| Attention and block | Certified intermediate ranges | Composed execution and numerical theorems. |
| Trained model | Frozen weights and certified token domain | Concrete logit bound and successful inference. |

The initial exponential experiment uses a degree-six Taylor polynomial with
binary64 coefficients and Horner evaluation.  Its extension uses division by
eight and three squarings.  Coefficient errors, underflow, and every rounded
operation enter the bounds.  A proof experiment determines the retained bound.
Each completed component remains runnable during subsequent work.

## Numerical investigation

The earlier investigation covered perturbed inputs, LayerNorm sensitivity,
checkpoint-specific ranges, and softmax score spread.  The records retain
the coarse logit bounds and their causes.  Further numerical work is deferred.

The [LayerNorm analysis](layernorm-analysis.md) records the pinned source
audit, endpoint perturbation identity, and implementation sequence.
The [GELU analysis](gelu-analysis.md) records its logistic identity and
binary64 error budget.  The [training implementation](../training/tiny-gpt2/README.md)
uses the approved CPU PyTorch backend.

The [real-valued model](../proofs/talos/lean/Project/TinyGpt2/Real.lean)
defines every stage of the audited architecture.  Its causal-prefix
theorem proves equal output at a position whenever the input prefixes
through that position agree.  The wider softmax computation proves a sum
of absolute probability errors of at most 10053 times 2^-52 for finite scores with active differences below
2^1023.  Its real input-perturbation theorem has multiplier two.  Checkpoint
range certificates prove finite hidden coordinates and all 256 finite
logits for every four-byte input.  The composed numerical theorem now
passes with B and normalization lower bounds as parameters.  Its
unconditional estimate is too coarse to certify precision.  A useful
precision guarantee remains open.  The CLI accepts runtime weights and B
through the proved checking and inference entry.
The complete generated-WAT inference execution theorem passes, including
termination, exact raw-bit output, checkpoint preservation, and its memory
reservation.

The [weight layout and arithmetic body](tiny-model-layout.md) record the
runtime tensor representation, compiled initialization tests, and remaining
model proof obligations.

Use the existing Wasmtime host and source-driven Talos registry.  Dependencies,
toolchains, and compiler semantics remain pinned to the current checkout.

## References

- [Binary64 arithmetic bounds](../proofs/talos/lean/Project/ProofKit/F64ArithmeticBounds.lean).
- [Guarded Horner proof](../proofs/talos/lean/Project/F64Horner2CheckedBits/README.md).
- [TorchLean model configuration](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/Examples/Models/Sequence/Gpt2.lean).
- [TorchLean activation definitions](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/Spec/Layers/Activation.lean).

## 128-byte implementation

The 128-position model keeps width four, two heads of width two, and one
block.  Its position table grows from 16 to 512 words, taking the total
parameter count from 2,488 to 2,984.  The sequence representation becomes
an array.  Nonempty prefixes through length 128 use their first positional
rows and return the final position's 256 logits.

Sequence softmax uses a maximum pass, the existing negative exponential,
a sum pass, and division.  The execution proofs must establish that each
pass computes its source definition and preserves the required memory.
Width-four projection, normalization, GELU, runtime weight checking, and
vocabulary output retain their existing arithmetic.  The source fixes
binary64 rounding and accumulation order.

Training exposes context sizes four, 64, and 128.  CPU tests check parameter
counts, causal-prefix equality, finite gradients, and input-length rejection.
The existing four-position artifact and the intermediate
[64-position checkpoint](../data/tiny-gpt2-64-v1/README.md) remain available.

- [x] Parameterize training and test the 128-position model.
- [x] Train and export the [128-position checkpoint](../data/tiny-gpt2-128-v1/README.md) on pinned Tiny Shakespeare.
- [x] Implement array-based inference and compare WASM with the Lean source.
- [ ] Prove exact execution of sequence traversal and softmax.
- [ ] Compose checked inference, termination, and memory guarantees.
- [ ] Publish the 128-byte CLI artifact with its checked proof.
