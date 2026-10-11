# Xorshift: Marsaglia's xorshift64

## What it is

[The program](Program.lean) is the 64-bit example of Marsaglia's paper "Xorshift RNGs" (2003):
`step x` applies `x ^^^ (x <<< 13)`, then `x ^^^ (x >>> 7)`, then `x ^^^ (x <<< 17)`, and
`advance n x` applies `step` `n` times.  The triple `(13, 7, 17)` is among Marsaglia's 275 triples
for which the matrix `T` of the step has order `2^64 - 1` among nonsingular 64 × 64 matrices over
GF(2).  [The compiled module](../../Verified/Examples/Xorshift.lean) is the verified compiler's
module of the two functions.

## What it shows

Each of the three xorshifts distributes over xor and is injective, since `d = d <<< a` or
`d = d >>> a` with `a > 0` forces every bit of `d` to 0, by induction on the bit position.  The step
is then a bijection that maps 0 to 0, so a nonzero state never becomes 0.  [The proofs](Period.lean)
work with the bit vectors of the words and use only the axioms `propext`, `Classical.choice`, and
`Quot.sound`.

| Theorem | Statement |
|---------|-----------|
| `step_xor` | `step (x ^^^ y) = step x ^^^ step y`. |
| `step_bijective` | `step` is a bijection on words. |
| `iterate_ne_zero`, `advance_ne_zero` | A nonzero state never becomes 0. |
| `xorshift_advance` | The module's bytes decode to the module, whose `advance` export computes `advance` without a trap, and `advance n x ≠ 0` for every nonzero `x`. |

## Running it

```sh
tools/leanrun --timeout 60m lake build Verified.Examples.Xorshift
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Verified.Examples.Xorshift \
  Verified.Examples.Xorshift.compiled.module build/verified/xorshift.wasm
build/tools/leanexe-wasmtime-host call build/verified/xorshift.wasm advance i64 i64:1 i64:1
```

The commands build the proofs, write the module, and call `advance 1 1` in the Wasmtime host, with
the setup of [the repository README](../../README.md#commands).  The call prints 1082269761, the
state after one step from 1.  After `tools/leanrun --timeout 60m lake build Verified`,
[`tests/verified/run.sh`](../../tests/verified/run.sh) writes every module of the verified compiler
and compares the cases of [`Verified/Examples/Cases.lean`](../../Verified/Examples/Cases.lean)
between the module and native Lean.

## Related examples

[`Lcg`](../Lcg/README.md) and [`ParkMiller`](../ParkMiller/README.md) are the other generators,
and [`Orbit`](../Orbit/README.md) holds the lemmas about iterates that the three share.
[SplitMix64](../Prng/README.md) mixes its state with xorshifts and multiplications by odd
constants, each a bijection on words.

## References

- G. Marsaglia, "Xorshift RNGs," *Journal of Statistical Software* 8(14), 2003,
  [doi:10.18637/jss.v008.i14](https://doi.org/10.18637/jss.v008.i14).
