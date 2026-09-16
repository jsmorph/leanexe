# GELU analysis

The [tiny transformer plan](tiny-transformer.md) uses the pinned TorchLean
tanh approximation:

```text
c = 44715 / 1000000
k = sqrt(2 / pi)
G(x) = x * (1 + tanh(k * (x + c*x^3))) / 2
```

## Real identities and domain

For a nonnegative magnitude a, define z(a) = 2*k*(a+c*a^3).
Then G(a) = a/(1+exp(-z(a))) and G(-a) = G(a)-a.
For a in [0, 3], k is less than 4/5 and z(a) is less than seven.
The existing exponential theorem on [-8, 0] therefore covers this interval
with room for coefficient and arithmetic errors.

## Binary64 calculation

Evaluate a squared, multiply by the rounded coefficient c, add one,
multiply by a, and multiply by the rounded coefficient 2*k.
Clear the computed argument's sign and set its negative sign before calling
the exponential.  This preserves the negative exponential domain at zero
and subnormal inputs.  Absolute-value contraction bounds the resulting
argument error against the nonnegative real z(a).

Add one to the exponential result and divide a by that sum.  For a negative
input, subtract a from the quotient.  All operations use the existing
binary64 semantics.  The checked absolute error is at most 1/80000 on
[-3, 3].  Mathlib's twenty-decimal bounds for pi bound the stored scale
coefficient's error by 10^-15.  The cubic argument's computed error is at
most 10^-10.  The exponential error is at most 1/290000 after argument
perturbation, and denominator error is at most 1/280000.  Division and the
negative-input subtraction complete the bound.

The checkpoint range investigation will determine whether the feed-forward
inputs fit this interval.  Wider inputs require a proved extension before
model integration.

For a at least three, z(a) is at least 2a.  The exponential series gives
exp(6) at least 300, and exp(2a-6) is at least 2a-5.  Thus exp(z(a)) is
at least 100a.  The exact identity G(a)-a = -a/(1+exp(z(a))) then bounds
the positive tail error by 1/100.  Symmetry gives the same bound for
replacing the negative tail by zero.  This provides a possible proved
extension to all finite inputs while retaining the tanh formula as the
real reference.  Its global error bound remains 1/100.  A separate theorem
gives the extended evaluator the sharper 1/80000 bound when its input lies
in [-3, 3].

Lean now checks both tail bounds and the extended evaluator's finite
output and error bound.  Its generated execution remains model integration
work.  A global derivative argument also proves |G(x)-G(y)| at most
4*|x-y| for all real inputs: the sigmoid contribution is at most one,
and the derivative's other term has magnitude at most three.

## Work

- [x] Prove the logistic identity, magnitude bound, and input perturbation.
- [x] Prove binary64 argument, exponential, and output errors.
- [x] Check generated-WAT execution and command-line examples.

The checked real perturbation theorem bounds |G(x)-G(y)| by 4*|x-y|
for x and y in [-3, 3].  It uses the global sigmoid derivative bound 1/4
and the cubic argument's Lipschitz bound four on that interval.

## Reference

[Pinned TorchLean activation specification](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/Spec/Layers/Activation.lean).
