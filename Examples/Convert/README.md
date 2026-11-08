# Convert: conversions between `Int64` and the floats

## Programs and specifications

[`Program.lean`](Program.lean) defines the conversions and a gain.  `toDouble a` and `toSingle a` are `a.toFloat` and `a.toFloat32`, which round the integer to the nearest binary64 or binary32 value with ties to even.  `ofDouble x` and `ofSingle x` are `x.toInt64`, which truncates toward zero and saturates at the bounds of `Int64`, with 0 for NaN.  `scale a k` is `(a.toFloat * k).toInt64`, a binary64 gain applied to an integer.  [`Spec.lean`](Spec.lean) states each result through WebAssembly's signed conversions as Talos defines them, in integer arithmetic on the bit fields: `expectedToDouble a` is `f64.convert_i64_s` of `a`'s word, `expectedToSingle a` is `f32.convert_i64_s`, `expectedOfDouble x` and `expectedOfSingle x` are `i64.trunc_sat_f64_s` and `i64.trunc_sat_f32_s` of `x`'s bits, and `expectedScale a k` composes `f64.convert_i64_s`, `f64.mul`, and `i64.trunc_sat_f64_s`.  `verified_compile compiled := [toDouble, toSingle, ofDouble, ofSingle, scale]` in [`Compiled.lean`](Compiled.lean) compiles the conversions through the word forms of [`Signed64Float.lean`](../../LeanExe/ProofKit/Signed64Float.lean), which use the unsigned conversions, so the module executes none of the four signed conversion instructions.

## Theorems

[`Proof.lean`](Proof.lean) proves the specifications from the equations of [`Signed64Wasm.lean`](../../LeanExe/ProofKit/Signed64Wasm.lean) between Lean's conversions and Talos's, and [`Compiled.lean`](Compiled.lean) composes them with the generated theorems.

| Theorem | Statement |
|---------|-----------|
| `toDouble_spec`, `toSingle_spec` | `(toDouble a).toBits = expectedToDouble a` and `(toSingle a).toBits = expectedToSingle a` for every `a`. |
| `ofDouble_spec`, `ofSingle_spec` | `(ofDouble x).toUInt64 = expectedOfDouble x` and `(ofSingle x).toUInt64 = expectedOfSingle x` for every `x`. |
| `scale_spec` | `(scale a k).toUInt64 = expectedScale a k` for every `a` and `k`. |
| `special_values` | The kernel's evaluation of the programs at the special values.  `ofDouble` gives 0 for NaN, -0, and -0.5, -1 for -1.5, `minValue` for `-2^63`, the double below it, and negative infinity, `2^63 - 1024` for the largest double below `2^63`, and `maxValue` for `2^63` and positive infinity, and `ofSingle` gives the same at the binary32 neighbors of `±2^63`, with `2^63 - 2^39` for the largest single below `2^63`.  `toDouble` rounds `2^53 + 1` and `2^53 + 3` and their negations to the even significands below and above them, and `maxValue` and `minValue + 1` to `±2^63`.  `toSingle` rounds `2^24 + 1`, `2^24 + 3`, and `-(2^24 + 1)` in the same way, and `2^62 + 2^38 + 1` and its negation up in magnitude to `±(2^62 + 2^39)`, where a rounding through binary64 would give `±2^62`. |
| `toDouble_call`, `toSingle_call` | Functions 2 and 3, called with `a`'s word from any store, return without a trap the bits `expectedToDouble a` or `expectedToSingle a` and leave the store unchanged. |
| `ofDouble_call`, `ofSingle_call` | Functions 4 and 5, called with `x`'s bits from any store, return without a trap the word `expectedOfDouble x` or `expectedOfSingle x` and leave the store unchanged. |
| `scale_call` | Function 6, called with `a`'s word and `k`'s bits from any store, returns without a trap the word `expectedScale a k` and leaves the store unchanged. |
| `convert_file`, `convert_file_decode` | `build/verified/convert.wasm` holds the module's encoding and decodes to the module, as [`File.lean`](File.lean) states. |

## AArch64 Images

[`Convert.lean`](../../tests/TestSupport/A64/Convert.lean) states `toDouble_runs`, `toSingle_runs`, `ofDouble_runs`, and `scale_runs` in the form `ProgramRuns`, from the compiler's theorems of the entries.  `ofSingle` takes a binary32 parameter, which the bare-metal `main` does not pass.  [`ImageFilesConvert.lean`](../../tests/TestSupport/A64/ImageFilesConvert.lean) joins them with the Images' bytes and the startup.

| Image | Theorem | Result |
|-------|---------|--------|
| `todouble.img` | `todouble_image` | `toDouble (-(2^53 + 3))`: the bits of `-(2^53 + 4)`, the tie rounded to the even significand. |
| `tosingle.img` | `tosingle_image` | `toSingle (-(2^62 + 2^38 + 1))`: the bits of `-(2^62 + 2^39)`, rounded once from the 64-bit magnitude. |
| `ofdouble.img` | `ofdouble_image` | `ofDouble` of the double below `-2^63`: the word of `minValue`. |
| `convscale.img` | `convscale_image` | `scale (-7) 0.5`: the word of -3, the truncation of -3.5 toward zero. |

Each theorem states that the Image writes to the UART the eight bytes of a word `w` and the status 0, that `w` is the specification's word for the arguments, and the specification's value, which the kernel computes.  `tests/baremetal/a64-images.sh` writes the Images, has the kernel check their theorems, and runs them under QEMU.

## Cases

[`Cases.lean`](Cases.lean) gives the inputs: the operands of the floor cases, the integers that round at a tie or past one at either width, each with its negation, and the floats of the special values.  [`SignedCases.lean`](../../Verified/Examples/SignedCases.lean) compares the exports with native Lean on every input, and `scale` on every integer with every gain of the cases, through `tests/verified/run.sh --cases convert`.
