# Verified numerical WASM demonstrations

The demonstrations accept binary64 words as sixteen-digit hexadecimal
strings and run the numerical computation in Wasmtime.  Each theorem concerns
the Talos model decoded from the generated WAT.  The manifest records the
corresponding WASM digest, and the runner checks it before execution.
Exact-byte proof packages are deferred.  JSON parsing, host loading, and
decimal display are outside the formal execution theorem.

## GELU

`gelu` accepts finite binary64 inputs in [-3, 3].  It returns a finite
result within 1/80000 of x*(1+tanh(sqrt(2/pi)*(x+0.044715*x^3)))/2.
The input perturbation theorem adds four times the input error when both
reference and decoded inputs lie in that interval.

```sh
tools/talos-artifact.js prepare gelu
tools/talos-proof.js check gelu
tools/numeric-demo.js gelu --value -1
tools/numeric-demo.js gelu --input data/numerical/gelu/minus-one.json
```

Negative one returns approximately -0.15880801373558184.  The evaluator uses
a logistic identity and the proved exponential.  The generated-WAT theorem
proves termination, exact status and result words, and complete store
preservation for every raw input.  The guard recognizes exactly the stated
finite interval.  Rejected input returns status one and a zero payload.
The [GELU analysis](../../plans/gelu-analysis.md) records the derivation.

## LayerNorm

`layernorm` accepts four inputs, four scales, and four biases, each in [-4, 4].
The real reference uses population variance and epsilon 1/100000.  The WASM
entry returns four finite values with absolute component error at most
1/1000000.  It rejects every other input with status one and four zero words.

```sh
tools/numeric-demo.js layernorm --values 0 1 2 3
tools/numeric-demo.js layernorm --values 2 2 2 2 --scale 1 1 1 1 --bias 1 2 3 4
```

Omitting scale and bias selects ones and zeros.  The first command returns
approximately [-1.3416354199689269, -0.447211806656309,
0.447211806656309, 1.3416354199689269].  The second returns [1, 2, 3, 4].
JSON supplies `values_bits`, `scale_bits`, and `bias_bits`, each containing
exactly four hexadecimal words.  Output includes `values_bits`, decimal
`values`, the rational error bound, theorem name, and binary digest.

```sh
tools/talos-artifact.js prepare layer_norm
tools/talos-proof.js check layer_norm
tools/numeric-demo.js layernorm --input data/numerical/layernorm/example.json
node test/numeric_demo.js
```

The computation averages two pairwise sums, centers once, averages the squared
centered values, adds rounded epsilon, takes a square root, divides, and
applies scale and bias.  Every operation rounds separately.  The numerical
proof includes epsilon conversion error, subnormal arithmetic, and constant
inputs.  `Project.LayerNorm.Spec.layerNorm_real_error` connects the bound to
terminating generated-WAT execution with complete store preservation.

`Project.LayerNorm.layerNorm_perturbed` adds upstream input and parameter
errors.  For coordinatewise input error δ, scale error η, bias error θ,
scale magnitude G, and a positive lower bound L on both endpoint standard
deviations, its bound is 1/1000000 + 2Gδ/L + 2η + θ.  The
[LayerNorm analysis](../../plans/layernorm-analysis.md) derives the endpoint
bound and records the remaining checkpoint-range investigation.

## Softmax

`softmax` accepts one to four scores in [-4, 4].  Decimal arguments run directly:

```sh
tools/numeric-demo.js softmax --scores 0 1 2
```

The host converts each decimal argument to binary64 before execution.  The
theorem concerns these decoded binary64 inputs.  JSON input instead supplies
their exact binary64 encodings as an array.  Array length selects the active prefix,
and the host pads the remaining input positions with zero.  The WASM entry
checks the count and all four score words.  It subtracts the active maximum,
evaluates the extended exponential, sums the weights in two pairs, and
divides each active weight by that total.  Masked outputs contain exact
positive-zero bits.

```sh
tools/talos-artifact.js prepare softmax
tools/talos-proof.js check softmax
tools/numeric-demo.js softmax --input data/numerical/softmax/example.json
```

The example encodes [0, 1, 2].  Its captured probability output is
[0.09003058303323568, 0.24472846855334776, 0.6652409484134166, 0].
The [extreme-score input](softmax/extremes.json) exercises [-4, 4].
The output includes four raw words, decimal values, active count, exact
rational bounds, theorem name, and binary digest.

The numerical theorem proves absolute error at most 1/50000 per component
against real exponential softmax of the decoded inputs.  Active outputs
are positive and finite.  Their sum differs from one by at most
32 times 2^-52, or 1/140737488355328.  The computed denominator lies in
[49/50, 5].  Out-of-domain inputs return status one and four zero words.

`Project.Softmax.shifted_reference` proves equality between the shifted
reference and standard exponential softmax.  `subtract_max` accounts for
rounded subtraction.  `compute_numerical` combines the exponential,
denominator, division, mask, and normalization bounds.  The registered
`Project.Softmax.Spec.softmax_real_error` theorem connects the result to
terminating generated-WAT execution with complete store preservation.

`Project.Softmax.Spec.softmax_input_error` extends that execution theorem
to perturbed input scores.  If each score differs from its real target by
at most delta, each output differs from the target softmax by at most
1/50000 + 2*delta.  The target scores may be any real values.

## Small exponential

`exp-small` accepts every binary64 input in [-1, 0], including signed zeros
and subnormals.  It returns status zero, a finite positive result, and an
absolute error bound of 1/4000 against real exponential.  Both signed zeros
return the exact bits of one.  Every other input returns status one and zero
payload bits.  The evaluator uses degree-six Taylor coefficients stored as
binary64 values and six Horner stages with separate multiplication and addition.

Generate and check the artifact from the repository root:

```sh
tools/talos-artifact.js prepare exp_small
tools/talos-proof.js check exp_small
node test/numeric_demo.js
```

Run negative one half:

```sh
tools/numeric-demo.js exp-small --input data/numerical/exp-small/half.json
```

The input is `{"x_bits":"bfe0000000000000"}`.  The captured output is:

```json
{"status":0,"bits":"3fe368b60b60b60c","value":0.6065321180555556,"absolute_error_bound":{"numerator":"1","denominator":"4000"},"theorem":"Project.ExpSmall.Spec.expSmall_real_error","wasm_sha256":"331de6537d47522498fa593afd5a973422c89208c6585c6777c61dfe7f26e877"}
```

With no `--input` argument the runner reads JSON from standard input.
The [rejection input](exp-small/rejected.json) contains positive one and
returns `{"status":1,"bits":"0000000000000000"}`.

## Extended exponential

`exp-wide` accepts every binary64 input in [-8, 0].  It divides by eight,
evaluates the small polynomial, and squares three times.  Its output is
finite, at least 1/100000, and within 1/300000 of the real exponential.
Both signed zeros return exactly one.  The domain guard rejects every
other input with status one and zero payload.

```sh
tools/talos-artifact.js prepare exp_wide
tools/talos-proof.js check exp_wide
tools/numeric-demo.js exp-wide --input data/numerical/exp-wide/minus-eight.json
```

`Project.ExpWide.Spec.expWide_real_error` connects the error and positivity
bounds to generated-WAT execution.  `Project.ExpWide.reduction` proves
that rounded division stays within the polynomial domain, using binary64
spacing at one and a mixed division error bound.  The shared
`F64Square.approximation` lemma propagates each reconstruction error.
`Project.ExpWide.perturbed_exp` bounds the exponential error caused by
perturbing a nonpositive reference input.

## Proofs and numerical bounds

| Theorem | Statement |
|---------|-----------|
| `Project.ExpSmall.polynomialReal_error` | Real polynomial approximation error at most 1/4410 on absolute input at most one. |
| `Project.ExpSmall.polynomial_roundoff` | Coefficient and rounded-evaluation error at most 211 times 2^-52. |
| `Project.ExpSmall.inDomain_iff` | The executable guard recognizes exactly finite binary64 inputs in [-1, 0]. |
| `Project.ExpSmall.expSmall_success` | Every input in the mathematical domain returns status zero and the polynomial result. |
| `Project.ExpSmall.Spec.expSmall_exact` | Every raw input terminates with the specified status and result, preserving the complete WASM store. |
| `Project.ExpSmall.Spec.expSmall_real_error` | Generated-WAT execution on the domain returns a positive finite result within 1/4000 of real exponential. |

The proof sources are in the [small exponential project](../../proofs/talos/lean/Project/ExpSmall/Spec.lean).
The runtime tests compare WASM with native execution of Talos's bit model
and cover endpoints, signed zeros, subnormals, infinities, NaNs, and rejection.
The host exponential comparison is empirical test evidence.  The test suite
also covers all four active lengths, maximum positions, mixed signs,
equal scores, masks, invalid counts, and decimal command-line input.
LayerNorm tests cover constant and nearly constant rows, affine parameters,
and rejection of invalid words in each of the twelve argument positions.
