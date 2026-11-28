# Reductions

| Family | Functions and evaluation order |
|---|---|
| [Word reductions](Word/Program.lean) | `sumArray`, `productArray`, and `xorArray` fold left from zero, one, and zero.  Arithmetic wraps modulo `2^64`. |
| [Binary64 reductions](Float64/Program.lean) | `total` sums left to right.  `largest` applies Lean's `max` left to right from negative infinity.  `select` sums the flagged entries.  `sumRange` recursively halves a word-indexed range. |

Each family's `Compiled` module proves that its Wasm code computes these Lean definitions.
Floating-point results preserve the specified operation order, including NaNs and signed zero.
Missing flags read as false, and missing numeric entries read as zero.  [The binary64 master
theorems](Float64/Master.lean) bound the error of each sum of finite terms whose magnitudes sum to
at most `2^1022`: `total` and `select`, left-to-right sums of `n` terms, lie within
`γ_(n-1) Σ |x_i|` of the exact sum, and `sumRange` within `γ_d Σ |x_i|` with
`d = ⌈log₂ (hi - lo)⌉`, where `γ_k = k / (2^53 - k)`.  [`SumError.lean`](SumError.lean) proves the
bound of a left-to-right sum for any binary format.  [The statistics section](../../../index.md#5-statistics) lists mean and
sum of squares.
