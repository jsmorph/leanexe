# Reductions

| Family | Functions and evaluation order |
|---|---|
| [Word reductions](Word/Program.lean) | `sumArray`, `productArray`, and `xorArray` fold left from zero, one, and zero.  Arithmetic wraps modulo `2^64`. |
| [Binary64 reductions](Float64/Program.lean) | `total` sums left to right.  `largest` applies Lean's `max` left to right from negative infinity.  `select` sums the flagged entries.  `sumRange` recursively halves a word-indexed range. |

Each family's `Compiled` module proves that its Wasm code computes these Lean definitions.
Floating-point results preserve the specified operation order, including NaNs and signed zero.
Missing flags read as false, and missing numeric entries read as zero.  These modules have no
summation-error theorem.  [The numerical index](../../../index.md#6-floating-point-folds) also lists
mean and sum of squares.
