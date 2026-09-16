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
must check the squared matrix norms using the decoded checkpoint words.
The binary64 proof must then add first-normalization, projection, and
score errors and show the computed spread remains below sixteen.

This argument covers all real embedding rows through the normalization
identities.  It avoids enumerating four-token contexts while retaining the
relationship between query and key coefficients.

## Remaining checks

- [ ] Check the normalized-row sum and squared-norm facts.
- [ ] Check the bilinear and linear score-difference estimate.
- [ ] Check the checkpoint's exact rational matrix-norm bounds.
- [ ] Include binary64 normalization, projection, and score errors.
- [ ] Bound the attention residual and feed-forward stages.
- [ ] Derive the complete logit error bound.
