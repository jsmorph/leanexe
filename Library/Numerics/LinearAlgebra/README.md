# Linear algebra

| Family | Functions |
|---|---|
| [Binary64](Float64/Program.lean) | `dot`, `axpy`, `grid`, `matVec`, `matMul`, `matMulT`, and `add`. |
| [Binary32](Binary32/Program.lean) | `scale32`, `axpyArray32`, `matVec32`, `add32`, and `linear32`. |

Matrices use row-major flat arrays and `UInt64` dimensions.  Index and dimension arithmetic wraps
modulo `2^64`.  Missing entries read as zero.  Dot products accumulate left to right with a
separate multiplication and addition.  `linear32` adds its bias after the dot product.

Output lengths follow the definitions.  Binary64 `axpy` returns the length of `ys`, while binary32
`axpyArray32` returns the length of `x`.  Vector addition returns the first input's length.
Matrix products return the requested row count or the word product of their output dimensions.

Each family's `Compiled` module proves execution, allocation, and trap-free statements under the
verified compiler's premises.  These statements preserve floating-point operation order.  Further
numerical-error bounds remain future work.  The [binary64 GPT](../../../Demos/Gpt/README.md) and
[binary32 GPT](../../../Demos/Gpt32/README.md) demos import these functions.
