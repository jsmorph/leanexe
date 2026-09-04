# Guarded Binary64 Quadratic Horner Example

This example is the numerical and control-flow rehearsal for the Euler
Rusanov artifact.  It accepts raw binary64 words `x`, `c₂`, `c₁`, and `c₀`,
checks that every magnitude is at most one half, and evaluates the explicitly
rounded expression

```text
(c₂ * x + c₁) * x + c₀
```

with two `f64.mul` and two `f64.add` instructions.

On success it returns status zero and the result bits.  On rejection it
returns status one and positive-zero bits without entering the floating-point
branch.  The accepted pure-model theorem proves the output finite and within
`3 * 2^-52` of the exact real quadratic.  The first stage's `2 * 2^-52` error
is attenuated by `|x| ≤ 1/2` before the second two-operation error is added.

`Numerical.lean` contains the total source-facing contract.  `Program.lean`
is generated from the compiler-emitted WAT and must not be handwritten.
`Execution.lean` and the completed `Spec.lean` will establish total,
store-preserving generated-WAT execution, an explicit small-step trace, and
the same numerical result contract.  Native floating-point execution remains
a regression oracle and is not proof evidence.

The case is intentionally registered as incomplete until generated-WAT
execution and exact-program-byte proof closure pass.  This does not make
release manifests, receipts, or self-host packaging gates for this branch.
