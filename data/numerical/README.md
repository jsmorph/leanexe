# Verified numerical WASM demonstrations

The demonstrations accept binary64 words as sixteen-digit hexadecimal
strings and run the numerical computation in Wasmtime.  Each theorem concerns
the Talos model decoded from the generated WAT.  The manifest records the
corresponding WASM digest, and the runner checks it before execution.
Exact-byte proof packages are deferred.  JSON parsing, host loading, and
decimal display are outside the formal execution theorem.

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
finite, at least 1/100000, and within 1/400 of the real exponential.
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
The host exponential comparison is empirical test evidence.
