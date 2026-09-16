# Exponential bounds on the trained score domain

The [trained checkpoint audit](../data/tiny-gpt2-v1/attention-audit.json)
contains a context with active score spread 12.117768731550278 in CPU
binary64 arithmetic.  The checked exponential extension covers [-16, 0],
retaining its 1/400 absolute error bound.  The internal softmax theorem
now covers spread at most sixteen.

## Derivation

The existing evaluator divides its input by eight, evaluates the degree-six
Taylor polynomial, and squares three times.  The earlier theorem covers
[-8, 0].  For the remaining interval [-16, -8], rounded division produces
a finite value y in [-2, -999/1000].  The lower endpoint follows from the
binary64 successor gap at magnitude two.  The upper endpoint allows the
division error without requiring exact division.

Put t = y+2.  The polynomial becomes

```text
P6(y) = 7/45 + t/15 + t^2/6 - t^3/18 + t^4/24 - t^5/120 + t^6/720.
```

For 0 ≤ t ≤ 1001/1000, pair the quadratic and cubic terms and the fourth
and fifth powers to obtain P6(y) ≥ 7/45.  Dropping the two negative terms
and bounding the remaining powers gives P6(y) ≤ 9/20.

A Horner step for |y| ≤ 2, accumulator magnitude at most 128, and
coefficient magnitude at most one has local rounding error at most
514 times 2^-52.  Its propagated error is twice the prior error plus the
coefficient error and local error.  Six steps give 32,509 times 2^-52.
The computed polynomial therefore lies in [1/10, 46/100].

Three rounded squarings preserve positivity.  Conservative intermediate
bounds give a final value between 1/1000000000 and 1/400.  The exact
exponential also lies between zero and 1/400 on [-16, -8].  These two
interval bounds imply absolute error at most 1/400.  Combining the tail
result with the existing theorem covers [-16, 0].

## Remaining checks

- [x] Check the Horner rounding bound for magnitude two.
- [x] Check the polynomial interval bounds and rounded division interval.
- [x] Check the three squarings and exponential tail bound.
- [x] Extend the internal softmax spread theorem to sixteen.
- [ ] Certify the trained model's score spread within that domain.

## Sharper bound for model composition

The existing 1/400 bound loses the dependence between the polynomial
remainder and the later squarings.  Put t = -x/8, so 0 ≤ t ≤ 2.
Taylor's remainder gives
`0 ≤ P6(-t) - exp(-t) ≤ t^7/5040`.
The eighth-power difference is therefore at most
`8 * (t * P6(-t))^7 / 5040`.

In the degree-seven Bernstein basis on [0, 2], the coefficients of
`t * P6(-t)` are
`[0, 2/7, 8/21, 2/5, 8/21, 22/63, 32/105, 14/45]`.
All lie between zero and 2/5.  The resulting exact-real approximation
bound is `64/24609375`, about 2.601 × 10^-6, throughout [-16, 0].
Lean checks the signed Taylor remainder, polynomial identity, and eighth-power
bound.  The polynomial is 8-Lipschitz on [-2, 2].  Rounded division therefore
adds at most 16 times 2^-52 to its error.  Together with coefficient and Horner
roundoff, the computed polynomial differs from P6(x/8) by at most 10^-10.
Three rounded squarings add at most 15 times 10^-10 to the exact eighth-power
error.  The resulting evaluator error is at most 1/300000 on [-16, 0].

- [x] Check the signed Taylor remainder and Bernstein bound.
- [x] Check the eighth-power error estimate.
- [x] Add division, coefficient, Horner, and squaring roundoff.
- [ ] Propagate the sharper bound through softmax and bounded GELU.
