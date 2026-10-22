# Xorshift: Marsaglia's xorshift64

## The step and jump-ahead by columns

[The program](Program.lean) is the 64-bit example of Marsaglia's paper "Xorshift RNGs" (2003).
`step x` applies `x ^^^ (x <<< 13)`, then `x ^^^ (x >>> 7)`, then `x ^^^ (x <<< 17)`, and
`advance n x` applies `step` `n` times.  `jump n x` computes the same state from the columns of the
step, its images of the powers of 2, with one squaring per bit of `n`.  `applyCols c x` is the xor
of the columns `c` at the set bits of `x`, `square c` gives the columns of the square of the map
with columns `c`, and `jumpPass` is one pass of `jump`.  The triple `(13, 7, 17)` is among
Marsaglia's 275 triples for which the matrix `T` of the step has order `2^64 - 1` among nonsingular
64 × 64 matrices over GF(2).  [The compiled module](Verified.lean) is the
verified compiler's module of `step`, `advance`, `applyCols`, `square`, `jumpPass`, and `jump`.

## Bijection, period, jump-ahead, and memory bound

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

[The jump proof](Jump.lean) works on `UInt64`: the words `2^i`, the columns of the identity,
decompose a word into its bits, so for a map `g` that distributes over xor, `applyCols` of its
columns computes `g`, and `square` of its columns gives those of `g ∘ g`.  After `k` passes,
`jump`'s state holds `step^[n % 2^k] x` and the columns of `step^[2^k]`.  The code releases each
pass's old columns.  The compiler's bound on the growth of `top` charges 568 bytes for each of the
65 blocks that `jump` builds, the 64 words, the length word, and the 48 bytes of a block's header,
and it ignores the reuse of freed blocks.  The count of the top bits over a period follows from the
bijection of the counts below `2^64 - 1` onto the nonzero words.

| Theorem | Statement |
|---------|-----------|
| `step_xor` | `step (x ^^^ y) = step x ^^^ step y`. |
| `step_bijective` | `step` is a bijection on words. |
| `iterate_ne_zero`, `advance_ne_zero` | A nonzero state never becomes 0. |
| `applyList_cols`, `jumpList_pows` | The columns of a map on words that distributes over xor give its image of every word, and the tables of repeated squares give its `m`-th iterate by one product per set bit of `m`. |
| `orbitCheck_eq`, `minimalPeriod_one` | The state 1 returns after `2^64 - 1` steps and not before. |
| `step_minimalPeriod` | From every nonzero state, `step` returns after `2^64 - 1` steps and not before. |
| `existsUnique_iterate`, `advance_existsUnique` | From every nonzero state, each nonzero state occurs at exactly one count below `2^64 - 1`. |
| `applyCols_columns`, `square_columns`, `jump_eq` | On `UInt64` words and arrays, the columns of a map that distributes over xor give its image of every word and the columns of its square, and `jump n x = advance n x`. |
| `advance_topBits` | From a nonzero state, over the `2^64 - 1` counts of a period, the top `j` bits of the state take each nonzero value `2^(64 - j)` times and the value 0 `2^(64 - j) - 1` times. |
| `jump_bound` | The compiler's bound on the growth of `top` during `jump` is 36,920 bytes, 568 for each of 65 blocks of 64 words. |
| `xorshift_advance` | The module's bytes decode to the module, whose `advance` export computes `advance` without a trap, `advance n x ≠ 0` for every nonzero `x`, and from every nonzero `x` each nonzero `y` occurs at exactly one count below `2^64 - 1`. |
| `xorshift_jump` | The module's bytes decode to the module, whose `jump` export computes `advance` without a trap when `top` can rise by 36,920 bytes within the memory's cap, and raises `top` by at most 36,920 bytes. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Random.Xorshift.Verified
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean Library.Random.Xorshift.Verified \
  Library.Random.Xorshift.compiled.module build/verified/xorshift.wasm
build/tools/leanexe-wasmtime-host call build/verified/xorshift.wasm advance i64 i64:1 i64:1
```

The commands build the proofs, write the module, and call `advance 1 1` in the Wasmtime host, with
the setup of [the repository README](../../../README.md#commands).  The call prints 1082269761, the
state after one step from 1.  After `tools/leanrun --memory-high 10G --timeout 12h lake build Verified Library`,
[`tests/verified/run.sh`](../../../tests/verified/run.sh) writes every module of the verified compiler
and compares the cases of [`Verified/Examples/Cases.lean`](../../../Verified/Examples/Cases.lean)
between the module and native Lean.

## Related examples

[`Lcg`](../Lcg/README.md) and [`ParkMiller`](../ParkMiller/README.md) are the other generators,
and [`Orbit`](../Orbit/README.md) holds the lemmas about iterates that the three share.
[SplitMix64](../SplitMix64/README.md) mixes its state with xorshifts and multiplications by odd
constants, each a bijection on words.

## References

- G. Marsaglia, "Xorshift RNGs," *Journal of Statistical Software* 8(14), 2003,
  [doi:10.18637/jss.v008.i14](https://doi.org/10.18637/jss.v008.i14).
