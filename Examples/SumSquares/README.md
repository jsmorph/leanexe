# SumSquares: a fold over binary64 values

## What it is

[The program](Program.lean) returns the sum of the squares of an array of `Float` values,
accumulated from the left: `xs.foldl (fun acc x => acc + x * x) 0.0`.  Each step rounds twice, once
after the square and once after the sum, so the result depends on the order of the elements.  [The
module definition](Module.lean) compiles `sumSquares` into the 1,450-byte `sumSquares.wasm`.

## What it shows

The compiler translates `Array.foldl` to a loop over the array's words, and the fold rule
`Stmt.fold_spec` proves the loop for any step function on words.  The step here is `IEEE64.add a
(IEEE64.mul e e)` on bit patterns, and `sumSquares_bits` proves that folding it over the elements'
bits gives the bits of Lean's fold.  The theorem holds bit for bit in the program's order of
summation, including overflow to infinity and NaN.

| Theorem | Statement |
|---------|-----------|
| `sumSquares_bits` | Folding the step over the bit patterns of `xs` gives the bits of `sumSquares xs`. |
| `sumSquares_implements` | Function 2 of `sumSquares.module` implements `sumSquares`: from any store that satisfies the runtime invariant, with the array in memory, a call returns the bits of `sumSquares xs` or stops at `unreachable`. |
| `sumSquares_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `sumSquares`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  An `Array Float` is stored as the elements' bit patterns, so
the host passes the array as words.  [The manual](../../docs/manual.md#folds) lists the folds the
compiler accepts.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.SumSquares.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.SumSquares.Module Examples.SumSquares.sumSquares.module \
  build/sumSquares/sumSquares.wasm
build/tools/leanexe-wasmtime-host call build/sumSquares/sumSquares.wasm sumSquares f64 \
  array-u64:4607182418800017408,4611686018427387904,4613937818241073152
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The array is `[1.0, 2.0, 3.0]`, and the call
prints 4624070917402656768, the bits of 14.0.  [`tests/modules/run.sh`](../../tests/modules/run.sh)
compares 52 cases of [`Cases.lean`](Cases.lean) with native Lean, including the empty array,
infinities, NaN, subnormal values, and small terms before and after a large one.

## Related examples

[`Mean`](../Mean/README.md) folds addition over the same kind of array and divides by the length.
[`SumArray`](../SumArray/README.md) has folds over words.  `dot` in [`Gpt`](../Gpt/README.md) sums
the products of two arrays with a loop over indices.  The LTG entries
[`float-array-fold`](../../ltg/entries/float-array-fold/README.md) and
[`array-fold-loop`](../../ltg/entries/array-fold-loop/README.md) describe the rules.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter 4, on
  the rounding error of summation and its dependence on order.
- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019.
