import LeanExe.Pipeline.Implements

/-!
The representation of Lean's `Int64`: its two's-complement word, `x.toUInt64`, as one `i64`.  With
this instance the generic instances give `Scalar Int64` as `[.i64 x.toUInt64]` and an
`Array Int64` as the array of the words, and the reflector reads `Int64` as the source type of
words with this flattening.  The instance lies outside `Implements.lean`, beside which `Flat Bool
UInt64` lies, because the compiler's own proofs never use it: the reflector imports it, and so does
every program that `verified_compile` reflects.
-/

namespace LeanExe.Pipeline

instance : Flat Int64 UInt64 := ⟨Int64.toUInt64⟩

end LeanExe.Pipeline
