import Examples.Increment.Program
import Examples.Increment.Spec
import LeanExe.IR.Combinators

/-! The program equals the specification, a fact about the Lean definitions that the theorems of
the verified compilation use. -/

namespace Examples.Increment

open LeanExe.IR

/-- The program computes the specification on every input that memory can hold. -/
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold compute expected
  by_cases hs : xs.size ≤ 8
  · have hle : xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_true, hs]
    apply Array.ext
    · rw [build_size, hn, Array.size_map]
    · intro i hi _
      rw [build_size, hn] at hi
      rw [Array.getElem_map, ← getElem!_pos (LeanExe.build _ _) i (by rw [build_size, hn]; exact hi),
        build_get (by rw [hn]; exact hi), UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi h),
        getElem!_pos xs i hi]
  · have hle : ¬ xs.size.toUInt64 ≤ 8 := by rw [UInt64.le_iff_toNat_le, hn]; simpa using hs
    simp only [hle, ite_false, hs]
    rfl

end Examples.Increment
