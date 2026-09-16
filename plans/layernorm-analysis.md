# LayerNorm analysis

This analysis supports the LayerNorm step in [Verified tiny transformer
inference](tiny-transformer.md).  The real-arithmetic argument precedes the
binary64 implementation.  The [real LayerNorm proofs](../proofs/talos/lean/Project/LayerNorm/Real.lean)
check centering, normalized magnitude, input perturbation, and affine parameter
perturbation.  Binary64 execution remains the next step.

## Reference and source audit

For a row x of width n, let μ(x) be its mean, c(x) = x − μ(x),
v(x) = Σ c(x)ᵢ²/n, and r(x) = √(v(x) + ε).  LayerNorm returns
γᵢ c(x)ᵢ/r(x) + βᵢ.  The selected model has n = 4 and ε = 1/100000.
Constant rows therefore return β over the reals.

The pinned TorchLean [public constructor](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/API/Seeded.lean)
and [runtime layer](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/Runtime/Autograd/Model/Layers/Normalization.lean)
use rational epsilon 1/100000 and enable learned scale and bias.  The
[causal model constructor](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/API/Models/CausalTransformer/Architecture.lean)
uses pre-normalized blocks and a final LayerNorm, with separate vocabulary
weights, attention output bias, and no query, key, or value biases by default.

The pinned [LayerNorm specification](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/Spec/Layers/Normalization/Core.lean)
centers the input, applies a variance reduction that centers again, and takes
the maximum of that variance and zero.  These steps reduce to the formula
above over the reals.  Their rounded evaluation order affects floating-point
output.  The LeanExe theorem will name its own operation tree and measure
error against the real formula.  Agreement with a TorchLean floating-point
backend requires a separate comparison.

## Perturbation identity

Let z = c(x), w = c(y), r = r(x), s = r(y), and ε > 0.  Centering gives

    Σ(zᵢ − wᵢ)² = Σ(xᵢ − yᵢ)² − n(μ(x) − μ(y))².

The identities Σzᵢ² = n(r² − ε) and Σwᵢ² = n(s² − ε) give

    Σ(zᵢ − wᵢ)²
      = rs Σ(zᵢ/r − wᵢ/s)² + n(r − s)²(1 + ε/(rs)).

Every discarded term is nonnegative.  Consequently,

    Σ(zᵢ/r − wᵢ/s)² ≤ Σ(xᵢ − yᵢ)²/(rs).

This endpoint bound needs no lower variance along an interpolating segment.
If both standard deviations exceed L > 0, the Euclidean amplification is
at most 1/L.  For width four and coordinatewise input error at most δ,
each normalized coordinate differs by at most 2δ/L.  The universal choice
L = √ε gives about 632.46δ.  With a certified variance lower bound v₀,
L = √(v₀ + ε) improves the estimate.  A constant row attains the limiting
Euclidean sensitivity 1/√ε in a nonzero mean-zero perturbation direction.

Each normalized coordinate has magnitude at most √n, hence at most two
for width four.  Scale and bias perturbations therefore add at most
2η + θ per coordinate when their respective errors are η and θ.
For a bound G on the perturbed scale, the composed component estimate is
2Gδ/L + 2η + θ.  Binary64 evaluation error must be added separately.

## Implementation sequence

- [x] Check centering, normalized magnitude, and the perturbation identity in Lean.
- [x] Check the width-four component bound, including affine parameter error.
- [ ] Define the binary64 operation tree and account for the rounded epsilon.
- [ ] Prove successful execution and roundoff bounds on an explicit input domain.
- [ ] Add the generated-WAT execution proof and command-line demonstration.
- [ ] Use checkpoint ranges to evaluate the composed bound before block integration.

The initial proofs keep epsilon symbolic and positive.  The executable domain
and checkpoint ranges remain separate obligations.  No trained checkpoint
has been selected or measured.
