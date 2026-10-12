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
is then a bijection that maps 0 to 0, so a nonzero state never becomes 0.  These proofs work with
the bit vectors of the words.

The period comes from the orbit of the state 1.  With
`N = 2^64 - 1 = 3 · 5 · 17 · 257 · 641 · 65537 · 6700417`, the kernel checks that 1 returns after
`N` steps and after no `N / q` steps for each of the seven prime factors `q`, so the minimal period
of 1 is `N`.  The orbit of 1 then holds all `N` nonzero words, and every nonzero state lies on it
with the same period.  The check computes these iterates by jump-ahead, from [the column
lemmas](Columns.lean): a map that distributes over xor is the xor of its columns, the images of the
powers of 2, at the set bits of its argument, so the columns of a square are the images of the
columns.  The kernel computes the 64 columns of the step, 63 squarings, and one product per set bit
of each of the eight counts, on natural numbers, in about 20 seconds.  [The proofs](Period.lean)
use only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

| Theorem | Statement |
|---------|-----------|
| `step_xor` | `step (x ^^^ y) = step x ^^^ step y`. |
| `step_bijective` | `step` is a bijection on words. |
| `iterate_ne_zero`, `advance_ne_zero` | A nonzero state never becomes 0. |
| `applyList_cols`, `jumpList_pows` | The columns of a map on words that distributes over xor give its image of every word, and the tables of repeated squares give its `m`-th iterate by one product per set bit of `m`. |
| `orbitCheck_eq`, `minimalPeriod_one` | The state 1 returns after `2^64 - 1` steps and not before. |
| `step_minimalPeriod` | From every nonzero state, `step` returns after `2^64 - 1` steps and not before. |
| `existsUnique_iterate`, `advance_existsUnique` | From every nonzero state, each nonzero state occurs at exactly one count below `2^64 - 1`. |
| `xorshift_advance` | The module's bytes decode to the module, whose `advance` export computes `advance` without a trap, `advance n x ≠ 0` for every nonzero `x`, and from every nonzero `x` each nonzero `y` occurs at exactly one count below `2^64 - 1`. |

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
