# Bucket: a float to word conversion

## What it is

[The program](Program.lean) returns the index of the histogram bucket that holds `x`, for buckets of
width `width` starting at `lo`: `((x - lo) / width).toUInt64`.  Lean's `Float.toUInt64` saturates,
so values below `lo` and NaN fall in bucket 0, and values beyond the last word give 2^64 − 1.  [The
module definition](Module.lean) compiles `bucket` into the 1,374-byte `bucket.wasm`, which takes
three `f64` arguments and returns an `i64`.

## What it shows

WebAssembly has a trapping conversion, `i64.trunc_f64_u`, and a saturating one,
`i64.trunc_sat_f64_u`.  The compiler emits the saturating form, whose results for NaN, negative
values, and values out of range match Lean's definition, and `F64Convert.toUInt` proves the match
for every input.  The subtraction and division use the binary64 lemmas of the other float examples.

| Theorem | Statement |
|---------|-----------|
| `bucket_implements` | Function 2 of `bucket.module` implements `bucket`: from any store that satisfies the runtime invariant, a call returns `bucket x lo width` or stops at `unreachable`. |
| `bucket_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `bucket`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The manual's table of word
operations](../../docs/manual.md#words-and-booleans) lists the conversion.  A width of 0 gives an
infinite or NaN quotient, which the conversion maps to 2^64 − 1 or 0.

## Running it

```sh
tools/leanrun --timeout 60m lake build Examples.Bucket.Verify
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Bucket.Module Examples.Bucket.bucket.module build/bucket/bucket.wasm
build/tools/leanexe-wasmtime-host call build/bucket/bucket.wasm bucket i64 \
  f64:4612811918334230528 f64:0 f64:4607182418800017408
```

The commands build the proofs, write the module, and call it in the Wasmtime host, with the setup of
[the repository README](../../README.md#commands).  The arguments are 2.5, 0.0, and 1.0, and the
call prints 2.  [`tests/modules/run.sh`](../../tests/modules/run.sh) compares 89 cases of
[`Cases.lean`](Cases.lean) with native Lean, including negative values, NaN, a zero width, and
quotients near and beyond 2^64.

## Related examples

[`Mean`](../Mean/README.md) converts a word to a float with `UInt64.toFloat`.
[`Shape`](../Shape/README.md) converts words to floats inside a sum type.  The LTG entry
[`float-arithmetic`](../../ltg/entries/float-arithmetic/README.md) describes the rules for float
expressions.

## References

- WebAssembly Core Specification,
  [numerics](https://webassembly.github.io/spec/core/exec/numerics.html), for `trunc_u` and
  `trunc_sat_u`.
- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019, on conversions to integer formats.
