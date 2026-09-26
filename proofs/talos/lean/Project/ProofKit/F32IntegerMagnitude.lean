import Project.ProofKit.F32IntegerExact
import Project.ProofKit.F32Absolute

namespace Project.ProofKit.F32IntegerExact

theorem conversion_magnitude (word : UInt32)
    (hAbs : (LeanExe.Signed32.decode word).natAbs < 2 ^ 24) :
    Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.ofInt32Bits word) =
      (LeanExe.Signed32.decode word).natAbs * 2 ^ 149 := by
  have h := conversion_exact word hAbs
  have ha : |(LeanExe.Signed32.decode word : ℝ)| = ((LeanExe.Signed32.decode word).natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    rfl
  have he : (Wasm.IEEE32.scaledMagnitude (LeanExe.Float32.ofInt32Bits word) : ℝ) / 2 ^ 149 =
      ((LeanExe.Signed32.decode word).natAbs : ℝ) := by
    rw [← F32Order.abs_value_scaledMagnitude, h.2, ha]
  have hr := (div_eq_iff (by positivity : (2 : ℝ) ^ 149 ≠ 0)).mp he
  exact_mod_cast hr

#print axioms conversion_magnitude
end Project.ProofKit.F32IntegerExact
