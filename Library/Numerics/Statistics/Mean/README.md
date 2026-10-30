# Mean: a fold, a length, and a conversion

## The mean of an array of floats

[The program](Program.lean) returns the arithmetic mean of an array of `Float` values: the sum,
accumulated from the left, divided by the length converted to `Float`.  The mean of the empty array
is `0.0 / 0.0`, which is NaN.  [The module definition](Module.lean) compiles `mean` into the
1,455-byte `mean.wasm`, and [the verified compilation](Compiled.lean) compiles it with the verified
compiler into a 1,515-byte module.

## Bits of the mean for every array

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
manual](../../../../docs/leanexe-manual.md#arrays) describes.  The result is the mean of the rounded sum, and the
theorem says nothing about its error relative to the exact mean.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Library.Numerics.Statistics.Mean.Verify
mkdir -p build/mean
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Numerics.Statistics.Mean.Module Library.Numerics.Statistics.Mean.mean.module build/mean/mean.wasm
build/tools/leanexe-wasmtime-host call build/mean/mean.wasm mean f64 \
  array-u64:4607182418800017408,4611686018427387904,4613937818241073152,4616189618054758400
build/tools/leanexe-wasmtime-host call build/mean/mean.wasm mean f64 array-u64:
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../../../README.md#commands).  The first array is `[1.0, 2.0, 3.0, 4.0]`, and
the call prints 4612811918334230528, the bits of 2.5.  The second call prints 9221120237041090560,
`0x7FF8000000000000`, the canonical NaN.  [`tests/modules/run.sh`](../../../../tests/modules/run.sh)
compares 52 cases of [`Cases.lean`](../../../../tests/TestSupport/Modules/Mean.lean) with native Lean.

## The verified compiler's module

`verified_compile compiled := [mean]` in [the verified compilation](Compiled.lean) compiles the same
definition.  The fold, the length, and the conversion allocate nothing, so `compiled.mean.bound_eq`
states the bound 0, and the generated `compiled.mean.implements` states that function 2 computes
`mean` without a trap from every store with the allocator invariant and a memory cap of at most
65,535 pages.  `mean_implements` of the LeanExe module allows a trap at `unreachable`, and
`compiled.mean.native` states the computation for the C function of the module's translation.

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

The call prints 4612811918334230528, as the LeanExe module's call does.  [The verified
driver](../../../../tests/verified/run.sh) runs the 52 arrays of
[`Cases.lean`](../../../../tests/TestSupport/Modules/Mean.lean) in Wasmtime against native Lean and
checks that no call allocates beyond the host's array.  [The native
driver](../../../../tests/native/verified.sh) runs them on the module's translation to C, compiled
with CompCert.

## Related examples

[`SumSquares`](../SumSquares/README.md) has the same fold with a different step.
[`Bucket`](../../../../Examples/Bucket/README.md) converts in the other direction, from `Float` to `UInt64`.
[`SumCount`](../../../../Examples/SumCount/README.md) reads the length of a word array.  The LTG entries
[`array-size`](../../../../ltg/entries/array-size/README.md) and
[`float-arithmetic`](../../../../ltg/entries/float-arithmetic/README.md) describe the rules.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter 4.
- WebAssembly Core Specification,
  [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
