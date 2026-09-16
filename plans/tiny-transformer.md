# Verified tiny transformer inference

This plan expands phase 14 of the [Development Plan](../plan.md).
The user authorized implementation, frequent commits and pushes, and
command-line demonstrations on 2026-09-16.  The first target is standard
exponential softmax.  The transported proposal informed this plan.

## Scope and proof boundary

Use the existing binary64 compiler and Talos semantics.  A completed component
includes caller-supplied command-line input, a WASM artifact, exact
generated-WAT execution, successful execution throughout its advertised
domain, and a real-arithmetic error bound.  Record the binary digest and the
theorem subject.  Exact-byte packages are deferred to later releases, as
authorized by the user.  The host input decoder and decimal display remain
outside the numerical theorem.  Hexadecimal words preserve the canonical input.

The first model has four byte-token positions, one pre-normalized block,
two attention heads of width two, model width four, and feed-forward width
eight.  Audit parameter layout, biases, LayerNorm epsilon, and evaluation
order before model integration.  The pinned TorchLean activation uses the
tanh GELU formula.  Training is outside the inference proof.

The user approved a proved 64-byte context as the subsequent target.
Complete the four-byte model's execution, checkpoint ranges, and composed
numerical bound first.  Parameterize new sequence and softmax lemmas by
length where practical.  The larger model will require array-based context
traversal, expanded positional embeddings, training, and new certificates.

## Component sequence

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

Component theorems must propagate perturbed inputs.  Investigate LayerNorm
sensitivity and checkpoint-specific range estimates before the full block's
execution proof.  For attention composition, express the useful softmax
domain through score spread.  Record cases where conservative estimates
produce an uninformative logit bound, together with their causes.

The [LayerNorm analysis](layernorm-analysis.md) records the pinned source
audit, endpoint perturbation identity, and implementation sequence.
The [GELU analysis](gelu-analysis.md) records its logistic identity and
binary64 error budget.  The [training implementation](../training/tiny-gpt2/README.md)
uses the approved CPU PyTorch backend.

The [real-valued model](../proofs/talos/lean/Project/TinyGpt2/Real.lean)
defines every stage of the audited architecture.  Its causal-prefix
theorem proves equal output at a position whenever the input prefixes
through that position agree.  The softmax computation now accepts a
proved active-score spread of at most sixteen in its internal numerical
theorem and propagates real score error with multiplier two.  Frozen
checkpoint ranges and full-model execution remain open.

The [weight layout and arithmetic body](tiny-model-layout.md) record the
runtime tensor representation, compiled initialization tests, and remaining
model proof obligations.

Use existing ProofKit arithmetic bounds, including their underflow terms.
Use the existing Wasmtime host and source-driven Talos registry.  Dependencies,
toolchains, and compiler semantics remain pinned to the current checkout.

## References

- [Binary64 arithmetic bounds](../proofs/talos/lean/Project/ProofKit/F64ArithmeticBounds.lean).
- [Guarded Horner proof](../proofs/talos/lean/Project/F64Horner2CheckedBits/README.md).
- [TorchLean model configuration](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/Examples/Models/Sequence/Gpt2.lean).
- [TorchLean activation definitions](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/Spec/Layers/Activation.lean).
