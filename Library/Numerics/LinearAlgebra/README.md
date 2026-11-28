# Linear algebra

| Family | Functions |
|---|---|
| [Binary64](Float64/Program.lean) | `dot`, `axpy`, `grid`, `matVec`, `matMul`, `matMulT`, and `add`. |
| [Binary32](Binary32/Program.lean) | `scale32`, `axpyArray32`, `matVec32`, `add32`, and `linear32`. |

Matrices use row-major flat arrays and `UInt64` dimensions.  Index and dimension arithmetic wraps
modulo `2^64`.  Missing entries read as zero.  Dot products accumulate left to right with a
separate multiplication and addition.  `linear32` adds its bias after the dot product.

The definitions determine the output lengths.  Binary64 `axpy` returns the length of `ys`, while binary32
`axpyArray32` returns the length of `x`.  Vector addition returns the first input's length.
Matrix products return the requested row count or the word product of their output dimensions.

Each family's `Compiled` module proves execution, allocation, and trap-free statements under the
verified compiler's premises.  These statements preserve floating-point operation order.

The master theorems in [`Float64/Master.lean`](Float64/Master.lean) and
[`Binary32/Master.lean`](Binary32/Master.lean) bound the rounding error of every export against
the exact real result, for a call of the compiled module.  For example, `dot_master` states that
`dot`, called on finite floats whose products have magnitudes summing to at most `2^1021`, returns
a finite float within `γ_n Σ |x_i y_i| + n / 2^1074` of the exact `Σ x_i y_i`, where
`γ_k = k / (2^53 - k)`.  `axpyArray32_master` and `matVec32_master` give the binary32 bounds for
`axpyArray32` and `matVec32`, with `γ_k = k / (2^24 - k)`.  Each family has a master theorem for
every function in the table above.

The [binary64 GPT](../../../Demos/Gpt/README.md) and [binary32 GPT](../../../Demos/Gpt32/README.md)
demos import these functions.
