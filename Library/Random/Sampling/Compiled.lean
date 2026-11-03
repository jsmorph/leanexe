import Library.Random.Sampling.Reservoir
import Verified.Reflect.Command

/-! The verified compiler's module of Algorithms P, S, and R.  `shuffle` borrows the word array and
consumes the array it shuffles, which the caller hands over as `Moved (Array UInt64)`: every
exchange is the array's last use, so the module shuffles the array in its own block.  `sample` and
`reservoir` borrow both arrays and build one array of `min n N` words.  The generated `trapFree`
theorems state that functions 4, 5, and 6 compute `shuffle`, `sample`, and `reservoir`, and
`shuffle_spec`, `sample_spec`, and `reservoir_spec` state their properties. -/

namespace Library.Random.Sampling

open Wasm LeanExe.Pipeline
open Library.Sorting.Heapsort (swap)

verified_compile compiled := [scale, swap, shuffle, sample, reservoir]

theorem shuffle_export :
    ({ name := "shuffle", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The generated bound is 0, so a call of `shuffle` does not raise `top`. -/
theorem shuffle_bound (us xs : Array UInt64) : compiled.shuffle.bound (us, { val := xs }) = 0 :=
  compiled.shuffle.bound_eq us xs

theorem sample_export :
    ({ name := "sample", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The module allocates one block, the `min n N` words of the result. -/
theorem sample_bound (us xs : Array UInt64) (n : UInt64) :
    compiled.sample.bound (us, xs, n) =
      Verified.blockCost (if n ≤ xs.size.toUInt64 then n else xs.size.toUInt64).toNat :=
  compiled.sample.bound_eq us xs n

theorem reservoir_export :
    ({ name := "reservoir", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The module allocates one block, the `min n N` candidates. -/
theorem reservoir_bound (us xs : Array UInt64) (n : UInt64) :
    compiled.reservoir.bound (us, xs, n) =
      Verified.blockCost (if n ≤ xs.size.toUInt64 then n else xs.size.toUInt64).toNat :=
  compiled.reservoir.bound_eq us xs n

#print axioms compiled.shuffle.trapFree
#print axioms shuffle_spec
#print axioms compiled.sample.trapFree
#print axioms sample_spec
#print axioms compiled.reservoir.trapFree
#print axioms reservoir_spec

end Library.Random.Sampling
