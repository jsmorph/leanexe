# Runtime weights and numerical bounds

The user approved a checkpoint-independent checker, clipping, and a bound
parameter B with target range [0, 10].  Reject nonfinite weights, invalid
array shapes, and invalid bounds with an empty output array.  Compare
inference with the real model using the clipped weights.  The
[transformer plan](tiny-transformer.md) retains the four-byte target before
the 64-byte extension.

## Numerical investigation

The [numerical audit](../training/tiny-gpt2/numerical_audit.py) preserves
the cancellation example and computes preliminary sensitivity estimates.
Its [recorded results](../data/tiny-gpt2-v1/numerical-audit.json) refer to the
current compiled artifact and an 80-digit reference calculation.  The
calculation uses Python's standard library.  These are numerical results.
The future Lean theorem must establish its own inequalities.

For width four, normalization before scale and bias has coordinate
magnitude at most two.  A common weight cap therefore gives normalized
magnitude 3B and query, key, and value magnitudes 12B^2.  Nonnegative
attention probabilities summing to one give first-residual magnitude
48B^3+3B.  Expansion has magnitude 12B^2+B.  GELU's magnitude bound gives
second-residual magnitude 144B^3+8B^2+4B.  At B = 10, the residual bounds
are 48,030 and 144,840.  Runtime proofs must include rounding margins.

Let L = sqrt(1/100000) and N = 2B/L.  The existing real perturbation
theorems give the following contributions when other stages are exact:

| Error source | Contribution to the final logit bound |
|--------------|---------------------------------------|
| GELU component error g | (8B) N (4B) g |
| Softmax coordinate error p, context length n | (12nB^2)(4B)(1+(4B)N(4)(8B))N(4B) p |

At B = 10 the first multiplier is about 2.02e7.  At context length four,
the second is about 3.93e18.  A softmax error budget of 1e-16 thus contributes
about 393 to this conservative estimate before adding other errors.  At
length 64 the coordinatewise sum gives a factor sixteen more.  These
estimates identify a need for sharper composition.  They do not determine
the smallest possible uniform error bound.

## Proposed arithmetic

The numerical prototype proposes a degree-eighteen Taylor polynomial for
exp on [-1, 0].  Halve a negative argument until it lies in that interval,
then square the result once per halving.  Arguments below -64 return zero,
with real absolute error at most exp(-64).  The remaining arguments need
at most six halvings and squarings.

GELU would evaluate its logistic formula through magnitude eight.  Larger
positive inputs return the input, and larger negative inputs return zero.
The negative branch within the interval would use -a*e/(1+e), avoiding
subtraction of the two nearly equal positive quantities a/(1+e) and a.
The real reference remains the audited tanh GELU formula.  Every tail,
coefficient, and rounded operation requires a proved error bound.

The prototype's largest measured errors are 8.27e-17 across 276 exponential
inputs and 1.11e-15 across 519 GELU inputs.  The cancellation-case logit
error falls from about 383.216 to 9.33e-11 in the Python binary64 prototype.
The production arithmetic has not changed.  The proposed numerical methods
await user confirmation.

## Implementation sequence

- [x] Preserve the cancellation case and calculate preliminary sensitivity terms.
- [x] Prove the parameterized scalar clipping operation and array checker at source level.
- [ ] Prove the checker's generated-WAT execution and memory use.
- [ ] Confirm and implement the revised numerical methods.
- [ ] Prove the wider component domains and their numerical errors.
- [ ] Refine the composed bound, accounting for normalization sensitivity.
- [ ] Prove the checked inference entry, including rejection and memory use.
- [ ] Expose checkpoint and bound arguments in the CLI and complete its tests.
- [ ] Reuse the checker and numerical results for the 64-byte model.
