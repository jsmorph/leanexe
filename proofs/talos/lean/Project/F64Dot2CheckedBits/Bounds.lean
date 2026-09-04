import Project.ProofKit.F64Bounds

/-!
# Raw binary64 bounds for the guarded two-term dot product

Compatibility aliases retain the original case-local API while the proof now
lives in the reusable proof kit shared by guarded binary64 entry points.
-/

namespace Project.F64Dot2CheckedBits.Bounds

/-- Clear the sign bit of a binary64 word, exactly as the LeanExe guard does. -/
abbrev f64AbsBits (bits : UInt64) : UInt64 :=
  Project.ProofKit.F64Bounds.f64AbsBits bits

/-- Proof-side copy of `LeanExe.Examples.Float64Bits.boundedByHalf`. -/
abbrev boundedByHalfBits (bits : UInt64) : Bool :=
  Project.ProofKit.F64Bounds.boundedByHalfBits bits

/-- Passing the source program's raw-bit guard implies both finiteness and the
real magnitude bound consumed by the binary64 numerical kernel theorems. -/
theorem boundedByHalf_spec (bits : UInt64)
    (hguard : boundedByHalfBits bits = true) :
    CodeLib.IEEE64.Finite bits ∧
      |CodeLib.IEEE64.value bits| ≤ (1 : ℝ) / 2 :=
  Project.ProofKit.F64Bounds.boundedByHalf_spec bits hguard

#print axioms boundedByHalf_spec

end Project.F64Dot2CheckedBits.Bounds
