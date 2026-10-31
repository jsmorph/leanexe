# Mean: a fold, a length, and a conversion

## The mean of an array of floats

[The program](Program.lean) returns the arithmetic mean of an array of `Float` values: the sum,
accumulated from the left, divided by the length converted to `Float`.  The mean of the empty array
is `0.0 / 0.0`, which is NaN.  [The verified compilation](Compiled.lean) compiles `mean` with the
verified compiler into a 1,515-byte module.

## Bits of the mean for every array

The body combines three compiled forms: the fold over the elements, the load of the array's length
word, and `UInt64.toFloat`, which `verified_compile compiled := [mean]` compiles to
`f64.convert_i64_u`.  The length word precedes the elements in the array's layout, which [the
verified compiler manual](../../../../docs/verified-manual.md#types) describes.  The fold, the
length, and the conversion allocate nothing, so `compiled.mean.bound_eq` states the bound 0, and the
generated `compiled.mean.implements` excludes the trap.

| Theorem | Statement |
|---------|-----------|
| `compiled.mean.implements` | Function 2 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, with an argument that represents `xs`, returns the bits of `mean xs` without a trap. |
| `compiled.mean.native` | C function of the module's translation computes `mean` as `compiled.mean.implements` states. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `mean`. |
| `mean_file`, `mean_file_decode` | `build/verified/mean.wasm` holds the encoding of `compiled.module` and decodes to the module of `compiled.bytes`, as [the file module](File.lean) states. |

`compiled.mean.implements` holds for every array, the empty one included, and it states the bits of
Lean's `mean`.  The result is therefore the mean of the rounded sum, and the theorem says nothing
about its error relative to the exact mean.  The generated `compiled.mean.native` states the
computation for the C function of the module's translation.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Statistics.Mean.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Statistics.Mean.Compiled Library.Numerics.Statistics.Mean.compiled.module \
  build/verified/mean.wasm
build/tools/leanexe-wasmtime-host call build/verified/mean.wasm mean f64 \
  array-u64:4607182418800017408,4611686018427387904,4613937818241073152,4616189618054758400
tests/verified/run.sh --cases mean
tests/native/verified.sh --module mean
```

The commands build the verified compilation and its theorems, write the module, call it in the
Wasmtime host, and run the tests, with the setup of [the repository
README](../../../../README.md#commands).  The array is `[1.0, 2.0, 3.0, 4.0]`, and the call prints
4612811918334230528, the bits of 2.5.  [The verified driver](../../../../tests/verified/run.sh) runs
52 arrays in Wasmtime against native Lean and checks that no call allocates beyond the host's array.
The arrays are `floatArrays` of [the host's test support](../../../../tests/TestSupport/Host.lean),
the empty array among them, and [the verified library
cases](../../../../tests/TestSupport/LibraryCases.lean) print them with the results of native Lean.
[The native driver](../../../../tests/native/verified.sh) runs them on the module's translation to
C, compiled with CompCert.  Without `--cases`, the verified driver also checks the file module
against the file it wrote, and it fails unless `mean_file` and `mean_file_decode` report only
`propext`, `Classical.choice`, and `Quot.sound`.

## Related examples

[`SumSquares`](../SumSquares/README.md) has the same fold with a different step.
[`Bucket`](../../../../Examples/Bucket/README.md) converts in the other direction, from `Float` to
`UInt64`.  [`SumCount`](../../../../Examples/SumCount/README.md) reads the length of a word array.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter 4.
- WebAssembly Core Specification,
  [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
