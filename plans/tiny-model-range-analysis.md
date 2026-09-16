# Trained model range analysis

The [trained checkpoint](../data/tiny-gpt2-v1/README.md) requires a proof
covering every four-byte context.  The retained CPU audits identify ranges
and counterexamples to the initial component domains.  This analysis
derives bounds that can become kernel-checked checkpoint certificates.

## Attention spread

Let z be a width-four row after centering and division by its LayerNorm
denominator, before scale and bias.  Positive epsilon implies
sum(z) = 0 and sum(z_i^2) ≤ 4.  These facts hold for every real input row.
The difference between two normalized rows therefore has Euclidean norm
at most four.

For one head, let G be the diagonal matrix of first-normalization scales,
β its bias, and Q and K the four-by-two query and key matrices.  Let P
subtract the coordinate mean.  Define

```text
A = P G Q
B = P G K
M = A Bᵀ
d = B (βᵀQ)ᵀ.
```

For normalized query z and key difference u, the score difference is
`(zᵀ M u + dᵀu) / sqrt(2)`.  Cauchy–Schwarz bounds its magnitude by
`(8 ||M||_F + 4 ||d||_2) / sqrt(2)`.

CPU binary64 calculations give these preliminary values:

| Head | Frobenius norm of M | Norm of d | Derived real spread bound |
|------|---------------------|-----------|---------------------------|
| First | 1.631984790988159 | 0.11738673508043507 | 9.563919925595199 |
| Second | 2.3579436386362085 | 0.3433360476076598 | 14.309644482239415 |

An exact certificate can use the shared rational bounds
`||M||_F ≤ 12/5`, `||d||_2 ≤ 7/20`, and `sqrt(2) ≥ 7/5`.
These imply a real spread bound of 103/7, below fifteen.  The certificate
checks the squared matrix norms using the decoded checkpoint words.
The binary64 certificate includes first-normalization, projection, and
score errors.  Each computed score differs from the real score on its
decoded embedding rows by at most 1/3000.  Adding twice this error to
103/7 keeps the computed spread below sixteen.

Lean checks the exact rational inequalities and transfers them to the
model's real scores in the [checkpoint attention certificate](../proofs/talos/lean/Project/TinyGpt2/CheckpointAttention.lean).
The [weight certificate](../proofs/talos/lean/Project/TinyGpt2/CheckpointBounds.lean)
also proves that all 2,488 words are finite with real magnitude at most four.

The [binary64 score certificate](../proofs/talos/lean/Project/TinyGpt2/CheckpointScore.lean)
combines these bounds.  The [embedding certificate](../proofs/talos/lean/Project/TinyGpt2/CheckpointEmbedding.lean)
proves that every byte token at each accepted position produces a finite
row within the first normalization domain.

The real argument covers all embedding rows through the normalization
identities.  It avoids enumerating four-token contexts while retaining the
relationship between query and key coefficients.

## First residual

The [output-projection certificate](../proofs/talos/lean/Project/TinyGpt2/CheckpointResidual.lean)
combines each head's value and attention-output matrices before bounding
magnitudes.  This retains the shared normalized input in both value
coordinates.  Exact rational checks give these bounds:

| Head | Centered coefficient norm | Projected bias magnitude | Head-output magnitude |
|------|---------------------------|--------------------------|-----------------------|
| First | 1/3 | 1/100 | 7/10 |
| Second | 5/6 | 3/25 | 9/5 |

Nonnegative attention weights with sum at most `mass` give output-projection
magnitude at most `(5/2)*mass`.  Real softmax weights sum to one.  Adding
embedding magnitude at most one and output bias magnitude at most 1/10
bounds every real first-residual component by 18/5.  The binary64 margin
for this residual remains open.

## Remaining checks

- [x] Check the normalized-row sum and squared-norm facts.
- [x] Check the bilinear and linear score-difference estimate.
- [x] Check the checkpoint's exact rational matrix-norm bounds.
- [x] Include binary64 normalization, projection, and score errors.
- [x] Bound the real attention residual.
- [ ] Include the attention-residual roundoff margin.
- [ ] Bound the feed-forward stages.
- [ ] Derive the complete logit error bound.
