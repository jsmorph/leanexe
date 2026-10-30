# Bucket: a float to word conversion

## A histogram bucket index

[The program](Program.lean) returns the index of the histogram bucket that holds `x`, for buckets of
width `width` starting at `lo`: `((x - lo) / width).toUInt64`.  Lean's `Float.toUInt64` saturates,
so a negative or NaN quotient gives bucket 0, and a quotient beyond the word range gives 2^64 − 1.  For a positive width, values below `lo` give bucket 0.  [The
module definition](Module.lean) compiles `bucket` into the 1,374-byte `bucket.wasm`, which takes
three `f64` arguments and returns an `i64`.

## The saturating conversion

WebAssembly has a trapping conversion, `i64.trunc_f64_u`, and a saturating one,
`i64.trunc_sat_f64_u`.  The compiler emits the saturating form, whose results for NaN, negative
values, and values out of range match Lean's definition, and `F64Convert.toUInt` proves the match
for every input.  The subtraction and division use the binary64 lemmas of the other float examples.

| Theorem | Statement |
|---------|-----------|
| `bucket_implements` | Function 2 of `bucket.module` implements `bucket`: from any store that satisfies the runtime invariant, a call returns `bucket x lo width` or stops at `unreachable`. |
| `bucket_bytes` | `encode` succeeds on the module, and the module that `decode` reads from the bytes implements `bucket`. |

The proofs are in [`Verify.lean`](Verify.lean), and they use only the axioms `propext`,
`Classical.choice`, and `Quot.sound`.  [The LeanExe compiler manual's table of word
operations](../../docs/leanexe-manual.md#words-and-booleans) lists the conversion.  A width of 0
gives an infinite or NaN quotient, which the conversion maps to 2^64 − 1 or 0.

## Building, running, and testing

```sh
tools/leanrun --timeout 60m lake build Examples.Bucket.Verify
mkdir -p build/bucket
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

## The verified compiler's module

`verified_compile compiled := [bucket]` in [the verified compilation](Compiled.lean) compiles the
same definition into the 1,398-byte `bucket.wasm` of [the module
registry](../../tests/verified/modules.txt).  The function allocates nothing, so the generated
`compiled.bucket.implements` states that function 2 returns `bucket x lo width` without a trap,
where `bucket_implements` allows a stop at `unreachable`.  The generated `compiled.bucket.native`
states the same of the C function of the module's translation, and the theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

| Theorem | Statement |
|---------|-----------|
| `compiled.bucket.implements` | Function 2 of `compiled.module`, called from any store with the allocator invariant and a memory cap of at most 65,535 pages, returns `bucket x lo width` without a trap. |
| `compiled.bytes` | `encode` succeeds on the module, its bytes decode to the module, and the module implements `bucket`. |
| `bucket_file`, `bucket_file_decode` | `build/verified/bucket.wasm` holds the module's encoding and decodes to the module, as [the file module](File.lean) states. |

```sh
tools/leanrun --timeout 60m lake build Examples.Bucket.Compiled
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Examples.Bucket.Compiled Examples.Bucket.compiled.module build/verified/bucket.wasm
build/tools/leanexe-wasmtime-host call build/verified/bucket.wasm bucket i64 \
  f64:4612811918334230528 f64:0 f64:4607182418800017408
tests/verified/run.sh --cases bucket
tests/native/verified.sh --module bucket
```

The call prints 2, as the LeanExe module's call does.  [The verified
driver](../../tests/verified/run.sh) runs the inputs of [`Cases.lean`](Cases.lean) in Wasmtime
against native Lean, and [the native driver](../../tests/native/verified.sh) runs them on the
module's translation to C, compiled with CompCert.  The cases state that a call allocates no block.

## Related examples

[`Mean`](../../Library/Numerics/Statistics/Mean/README.md) converts a word to a float with `UInt64.toFloat`.
[`Shape`](../Shape/README.md) converts words to floats inside a sum type.  The LTG entry
[`float-arithmetic`](../../ltg/entries/float-arithmetic/README.md) describes the rules for float
expressions.

## References

- WebAssembly Core Specification,
  [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019.
