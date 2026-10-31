# SumSquares: a fold over binary64 values

## A sum of squares with two roundings per step

[The program](Program.lean) returns the sum of the squares of an array of `Float` values,
accumulated from the left: `xs.foldl (fun acc x => acc + x * x) 0.0`.  Each step rounds twice, once
after the square and once after the sum, so the result depends on the order of the elements.  [The
verified compilation](Compiled.lean) compiles `sumSquares` with the verified compiler into a
1,516-byte module.

## Lean's bits in the program's order of summation

`verified_compile compiled := [sumSquares]` translates `Array.foldl` to a loop over the array's
words.  The fold allocates nothing, so the generated `compiled.sumSquares.implements` excludes the
trap, and it holds bit for bit in the program's order of summation, including overflow to infinity
and NaN.  An `Array Float` holds the elements' bit patterns, so the host passes the array as
words.  [The verified compiler manual](../../../../docs/verified-manual.md#loops-and-builds) states
the folds that the verified compiler accepts.

| Theorem | Statement |
|---------|-----------|
| `compiled.sumSquares.implements` | Function 2 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, with an argument that represents `xs`, returns the bits of `sumSquares xs` without a trap. |
| `compiled.sumSquares.native` | C function of the module's translation computes `sumSquares` as `compiled.sumSquares.implements` states. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `sumSquares`. |
| `sumSquares_file`, `sumSquares_file_decode` | `build/verified/sumSquares.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`, as [the file module](File.lean) states. |

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Statistics.SumSquares.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Statistics.SumSquares.Compiled \
  Library.Numerics.Statistics.SumSquares.compiled.module build/verified/sumSquares.wasm
build/tools/leanexe-wasmtime-host call build/verified/sumSquares.wasm sumSquares f64 \
  array-u64:4607182418800017408,4611686018427387904,4613937818241073152
tests/verified/run.sh --cases sumSquares
tests/native/verified.sh --module sumSquares
```

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, and run the tests, with the setup of [the repository
README](../../../../README.md#commands).  The array is `[1.0, 2.0, 3.0]`, and the call prints
4624070917402656768, the bits of 14.0.  [The verified driver](../../../../tests/verified/run.sh)
runs 52 arrays in Wasmtime against native Lean and checks that no call allocates beyond the host's
array.  The arrays are `floatArrays` of [the host's test
support](../../../../tests/TestSupport/Host.lean), and they include the empty array, infinities,
NaN, subnormal values, and small terms before and after a large one.  [The verified library
cases](../../../../tests/TestSupport/LibraryCases.lean) print them with the results of native Lean,
and [the native driver](../../../../tests/native/verified.sh) runs them on the module's translation
to C, compiled with CompCert.  Without `--cases`, the verified driver also checks the file module
against the file it wrote, and it fails unless `sumSquares_file` and `sumSquares_file_decode` report
only `propext`, `Classical.choice`, and `Quot.sound`.

## Related examples

[`Mean`](../Mean/README.md) folds addition over the same kind of array and divides by the length.
[`SumArray`](../../../../Examples/SumArray/README.md) has folds over words.  `dot` in [the binary64
linear-algebra library](../../LinearAlgebra/README.md) sums the products of two arrays with a loop
over indices.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter 4.
- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019.
