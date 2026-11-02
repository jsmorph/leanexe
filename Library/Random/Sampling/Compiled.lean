import Library.Random.Sampling.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of Algorithm P.  `shuffle` borrows the word array and consumes
the array it shuffles, which the caller hands over as `Moved (Array UInt64)`: every exchange is the
array's last use, so the module shuffles the array in its own block.  The generated
`compiled.shuffle.trapFree` states that function 4 computes `shuffle`, and `shuffle_spec` states
the properties of `shuffle`. -/

namespace Library.Random.Sampling

open Wasm LeanExe.Pipeline
open Library.Sorting.Heapsort (swap)

verified_compile compiled := [scale, swap, shuffle]

theorem shuffle_export :
    ({ name := "shuffle", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The module allocates nothing: it shuffles the array in its own block. -/
theorem shuffle_bound (us xs : Array UInt64) : compiled.shuffle.bound (us, { val := xs }) = 0 :=
  compiled.shuffle.bound_eq us xs

#print axioms compiled.shuffle.trapFree
#print axioms shuffle_spec

end Library.Random.Sampling
