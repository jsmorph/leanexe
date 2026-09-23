# Cached GPT-2 numerical comparison

`Session.trace_error` bounds the quantized and FP32 Lean recurrences on a common token sequence, with each recurrence retaining its own computed cache.  The bound covers quantized embedding lookup, twelve transformer blocks, final normalization, and all 50,257 vocabulary logits.  `Session.choices_agree` proves equal first-index greedy choices when every FP32 winning margin exceeds the sum of the two relevant component bounds.  Both theorems enter the registered package audit through aliases in the complete specification.

## Composition and assumptions

| Component | Bound | Required numerical evidence |
|-----------|-------|-----------------------------|
| Embedding | Weight reconstruction, FP32 multiplication, and both position additions | Export relation, retained position words, finite operands, and raw multiplication/addition ranges |
| Learned projection | Incoming activation error, local quantization and weight errors, exact 64-term integer dot, two FP32 rescalings, ordered group additions, and bias | Local reconstruction inequalities, valid signed bytes, finite scales, raw arithmetic ranges, and retained bias equality |
| LayerNorm | Ordered mean and variance, centering, epsilon, square root, reciprocal, gamma, and beta | Finite inputs and parameters, raw arithmetic ranges, positive root/denominator lower bounds, and retained parameter equality |
| Attention | Query–key dot, scale, shifted exponential, softmax, and probability–value dot | Historical/current cache bounds, finite intermediates, maximum dominance, exact exponential reduction, and positive denominator lower bounds |
| Residual/GELU | Both FP32 residual additions and rounded GELU branches with input perturbation | Finite inputs, raw arithmetic ranges, exponential conditions, and positive denominator lower bounds |
| Cache/session | Maximum of historical error and each new key/value error, followed through the shared prefix | Successful quantized steps, represented cache sizes, valid tokens/positions, and the per-step evidence above |

`Entry.Parameters` names the arithmetic exponents and reconstruction bounds.  `Entry.Ranges` states their obligations against the actual source intermediates.  `Session.Conditions` follows those obligations through the two evolving caches.  `Session.errorTrace` computes the resulting per-position, per-logit real bounds.  The induction starts with zero error for two empty caches.

The exponential theorem includes the degree-18 polynomial remainder, rounded coefficients, six reductions/squarings, and the cutoff below minus 64.  Its reduction equality is an explicit premise.  The GELU theorem includes both quotient branches and uses the conservative `1/100` real tail estimate at the magnitude-eight cutoff.  The real LayerNorm and softmax reference computations serve as intermediate comparisons.  Both the quantized and FP32 rounding errors contribute to the final difference bound.

The [raw-word range checkers](../../ProofKit/F32RangeCertificate.lean) supply sound Boolean checks for addition, subtraction, multiplication, division, square root, positive absolute denominator bounds, and exact power-of-two rescaling.  Their arithmetic uses integers decoded from FP32 words.  A successful operation check supplies a finite output and the corresponding real rounding bound.

## Measured evidence

The [checkpoint and activation records](../../../../../../data/gpt2-quantized-v1/certificates/README.md) check the exported weights and every captured group64 activation quantizer across 229 retained prefixes.  The activation record checks 233,580 groups and 14,949,120 coefficients.  Its local reconstruction bound includes clipping and division rounding.

The normalization checker supplies all `LayerNormPair.Ranges` premises for each of 11,450 captured normalizations.  It checks actual ordered mean and variance sums, centering, both divisions, epsilon addition, square root, reciprocal, normalization, gamma, and beta.  Its proved conversion uses a denominator lower bound of `1/1000`.  A separate theorem proves the corresponding real-reference root lower bound for every reference input.  Capture reproduces every FP32 and quantized retained logit hash.

All 16,883,712 captured GELU inputs pass the native checker.  Its soundness theorem supplies the argument, exponential, and quotient ranges, with a denominator lower bound of one.  The checker includes exact reduction and every Horner and squaring operation.

The retained greedy certificates use measured logit pairs and exact integer error bounds.  Their 183 successful common-offset certificates establish individual greedy choices.  These certificates do not instantiate `Session.errorTrace`.  Attention range evaluation, projection range instances, and evaluation of the propagated bound remain open.

## Checking

The focused numerical target is `Project.Gpt2QuantizedCached.Numerical.Greedy`.  The complete specification imports it, the checkpoint relation, and the range-checker soundness declarations.  The registered binary package audits `Spec.cached_session_logit_bound` and `Spec.cached_session_greedy` alongside the execution theorems.  Accepted declarations use `propext`, `Classical.choice`, and `Quot.sound`.
