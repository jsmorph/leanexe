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

The [parameterized range proofs](../proofs/talos/lean/Project/TinyGpt2/WeightBounds.lean)
establish these real-model bounds for every nonnegative B.  They also
bound score spread by 288 sqrt(2) B^4 and every real logit by 12B^2+B.
The [clipped-parameter theorem](../proofs/talos/lean/Project/TinyGpt2/ClippedParameters.lean)
connects every accepted runtime array to those hypotheses through all
2,488 parameter offsets.

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

The [weighted attention proofs](../proofs/talos/lean/Project/Softmax/WeightedPerturbation.lean)
now establish a context-independent real perturbation bound.  If values
have magnitude at most M, score errors are at most d, and value errors
are at most e, attention error is at most 2Md+e.  The sum of absolute
probability changes is at most 2d.  A separate theorem bounds the weighted
error from normalizing approximate exponential weights by 2Mr when each
weight has relative error at most r and both sums are positive.  Rounding
the sum, division, and weighted accumulation adds further errors.

The [complete checker theorem](../proofs/talos/lean/Project/F64Clip/Prepare.lean)
proves generated-WAT termination and exact output for arbitrary runtime
arrays.  It preserves the input and page count when 48+8(n+1) reserved
bytes fit after the input and the allocator free list is empty.  Accepted
output has finite values equal to the real clamp and bounded by B.
The [allocation-state theorem](../proofs/talos/lean/Project/F64Clip/Prepared.lean)
also exposes the final allocator counters, output ownership header,
preserved memory below the allocation, and unchanged store fields.

The [wider LayerNorm proof](../proofs/talos/lean/Project/LayerNorm/Wide.lean)
uses input magnitude X and scale and bias magnitude B.  For X at least one,
B in [0, 10], and 504X^2+1 below 2^1022, it proves finite output,
magnitude at most 3B+(254B+2)u, and component error at most
(16000BX+254B+2)u, where u = 2^-52.  At X = 200,000 and B = 10,
the error bound is below 7.11e-6.  The
[runtime-weight adapter](../proofs/talos/lean/Project/TinyGpt2/RuntimeNorm.lean)
derives its parameter hypotheses from checker acceptance and clipping.
The proof accounts for centering error separately from the rounding of
squares, averaging, the denominator, division, and the final affine map.
It changes no numerical operation.

The [runtime inference range theorem](../proofs/talos/lean/Project/TinyGpt2/RuntimeLogits.lean)
proves that every accepted clipped array produces 256 finite source-model
logits of magnitude at most 1,260 for every four-byte input.  The proof
derives finite loaded parameters, bounds every intermediate operation,
and uses the wider numerical components.  It requires no checkpoint facts.
The shared affine bounds take the product magnitude as a parameter, and
the normalization perturbation theorem retains an explicit denominator
lower bound.

The [composed source error theorem](../proofs/talos/lean/Project/TinyGpt2/NumericalLogits.lean)
and [numerical execution theorem](../proofs/talos/lean/Project/TinyGpt2Infer/Numerical.lean)
pass.  Their error formula takes B and positive lower bounds for the three
normalization stages.  Each lower bound must cover both the decoded computed
input and the corresponding real input.  The square root of the epsilon
floor always qualifies.  The formula accounts for all rounded operations,
coefficient errors, exponential tails, activation approximation, and input
perturbation through every stage.

The epsilon-floor formula evaluates to about 320.304 at B = 1, 1.733e7 at
B = 2.5, and 2.934e14 at B = 10.  These estimates are too coarse to certify
precision.  Repeated worst-case normalization sensitivity dominates the
composition.  The formulas accept larger certified denominator lower bounds.
A useful precision certificate remains open.

The combined entry compiles and passes 768 WASM logit comparisons and eight
rejection tests.  Its source rejection and numerical theorems pass.  Checked
function-region equality reuses the scalar checker, hidden-state, and logit
execution proofs.  The internal preparation call now has a complete proof
for its owner and data-pointer results.  The internal inference call now
proves termination, all 256 logits, and input preservation under the same
277,560-byte output reservation.  The enclosing entry proves exact output,
termination, and memory preservation for every accepted or rejected input.
Its numerical corollary compares accepted logits with the real model using
clipped weights, with B and normalization floors as parameters.

## Approved arithmetic

The user approved a degree-eighteen Taylor polynomial for
exp on [-1, 0].  Halve a negative argument until it lies in that interval,
then square the result once per halving.  Arguments below -64 return zero,
with real absolute error at most exp(-64).  The remaining arguments need
at most six halvings and squarings.

GELU evaluates its logistic formula through magnitude eight.  Larger
positive inputs return the input, and larger negative inputs return zero.
The negative branch within the interval uses -a*e/(1+e), avoiding
subtraction of the two nearly equal positive quantities a/(1+e) and a.
The real reference remains the audited tanh GELU formula.  Every tail,
coefficient, and rounded operation requires a proved error bound.

The prototype's largest measured errors are 8.27e-17 across 276 exponential
inputs and 1.11e-15 across 519 GELU inputs.  The cancellation-case logit
error falls from about 383.216 to 9.33e-11 in the Python binary64 prototype.
The component implementations and proofs are complete.  The command-line
inference artifact now uses these methods, with a complete generated-WAT
execution proof and checkpoint finite-output certificate.  The cancellation
case has measured WASM error 9.325e-11 against the 80-digit reference,
compared with 383.216 for the previous artifact.

The [new exponential numerical theorem](../proofs/talos/lean/Project/ExpNeg/Numerical.lean)
proves finite, positive output and relative error at most 4029u on [-64, 0].
The shared exact-halving theorem removes reduction roundoff.  Repeated
squaring carries relative error, including multiplication underflow.
Below -64, the output is zero and its absolute error is at most exp(-64),
which the proof bounds by 1e-27.  The registered generated-WAT theorem
proves exact output, rejection, termination, store preservation, and the
combined numerical bound.

The [wider GELU source theorem](../proofs/talos/lean/Project/GeluWide/Bounds.lean)
proves finite output for every finite input and absolute error at most
200000u, below 4.45e-11.  Its tail error is at most 1e-18.  The core
uses the new exponential and avoids cancellation in its negative branch.
The input-perturbation theorem adds four times the input error.  Its
generated-WAT theorem proves exact output, rejection, termination, and
complete store preservation.  The inference proof reuses this theorem.

The [wider softmax theorem](../proofs/talos/lean/Project/SoftmaxWide/Spec.lean)
proves a sum of absolute probability errors at most 10053u and normalization
error at most 52u.  It accepts finite scores whose active differences are
below 2^1023.  Weight error is relative, with an additive 1e-27 tail term.
The shared normalization result works over any finite index type.  The
four-position source and generated-WAT proofs are complete, including their
integration into the inference artifact.

## Implementation sequence

- [x] Preserve the cancellation case and calculate preliminary sensitivity terms.
- [x] Prove the parameterized scalar clipping operation and array checker at source level.
- [x] Prove real-model ranges and connect them to accepted clipped arrays.
- [x] Prove generated-WAT scalar clipping and complete array validation.
- [x] Prove the checker's generated-WAT execution and memory use.
- [x] Confirm the revised numerical methods.
- [x] Implement and verify the revised numerical methods.
- [x] Prove the wider component domains and their numerical errors.
- [x] Prove LayerNorm's wider domain and runtime-weight error bound.
- [x] Prove context-independent attention perturbation and relative normalization bounds.
- [x] Prove the composed error bound with explicit normalization sensitivity.
- [ ] Obtain a useful precision certificate from sharper numerical information.
- [x] Prove the checked inference entry, including rejection and memory use.
- [ ] Expose checkpoint and bound arguments in the CLI and complete its tests.
- [ ] Reuse the checker and numerical results for the 64-byte model.
