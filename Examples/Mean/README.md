# Mean: a fold, a length, and a conversion

## What it is

[The program](Program.lean) returns the arithmetic mean of an array of `Float` values: the sum,
accumulated from the left, divided by the length converted to `Float`.  The mean of the empty array
is `0.0 / 0.0`, which is NaN.  [The module definition](Module.lean) compiles `mean` into the
1,455-byte `mean.wasm`.

## What it shows

The body combines three compiled forms: the fold over the elements, the load of the array's length
word, and `UInt64.toFloat`, which compiles to `f64.convert_i64_u`.  `sum_bits` proves that the fold
of `IEEE64.add` over the bits gives the bits of Lean's sum, and `mean_bits` adds the division by the
converted length, with `F64Convert.toBits_toFloat` for the conversion.  The theorem holds for every
array, the empty one included.

| Theorem | Statement |
|---------|-----------|
| `sum_bits` | Folding `IEEE64.add` over the bit patterns of `xs` gives the bits of Lean's left-to-right sum. |
| `mean_bits` | The sum's bits divided by the converted length give the bits of `mean xs`. |
| `mean_implements` | Function 2 of `mean.module` implements `mean`: from any store that satisfies the runtime invariant, with the array in memory, a call returns the bits of `mean xs` or stops at `unreachable`. |
| `mean_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `mean`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  The length is a word of the array's layout, which [the
manual](../../docs/manual.md#arrays) describes.  The result is the mean of the rounded sum, and the
theorem says nothing about its error relative to the exact mean.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Mean.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Mean.Module Examples.Mean.mean.module build/mean/mean.wasm
build/tools/leanexe-wasmtime-host call build/mean/mean.wasm mean f64 \
  array-u64:4607182418800017408,4611686018427387904,4613937818241073152,4616189618054758400
build/tools/leanexe-wasmtime-host call build/mean/mean.wasm mean f64 array-u64:
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The first array is `[1.0, 2.0, 3.0, 4.0]`, and
the call prints 4612811918334230528, the bits of 2.5.  The second call prints 9221120237041090560,
`0x7FF8000000000000`, the canonical NaN.  [`tests/modules/run.sh`](../../tests/modules/run.sh)
compares 52 cases of [`Cases.lean`](Cases.lean) with native Lean.

## Related examples

[`SumSquares`](../SumSquares/README.md) has the same fold with a different step.
[`Bucket`](../Bucket/README.md) converts in the other direction, from `Float` to `UInt64`.
[`SumCount`](../SumCount/README.md) reads the length of a word array.  The LTG entries
[`array-size`](../../ltg/entries/array-size/README.md) and
[`float-arithmetic`](../../ltg/entries/float-arithmetic/README.md) describe the rules.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter 4.
- WebAssembly Core Specification,
  [numerics](https://webassembly.github.io/spec/core/exec/numerics.html), for `convert_u`.
