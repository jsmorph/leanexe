import Examples.Lookup.Program
import Examples.Lookup.Spec
import LeanExe.Dialect.Lemmas

/-! The program equals the specification, a fact about the Lean definitions that the theorems of
the verified compilation use. -/

namespace Examples.Lookup

/-- The program computes the specification on every input that memory can hold. -/
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold compute expected
  dsimp only
  by_cases hs : xs.size = 21
  · simp only [hs, bne_self_eq_false, Bool.false_eq_true, ite_false, LeanExe.loop]
    by_cases h1 : xs[1]! = xs[0]!
    · simp [h1]
    by_cases h2 : xs[3]! = xs[0]!
    · simp [h1, h2]
    by_cases h3 : xs[5]! = xs[0]!
    · simp [h1, h2, h3]
    by_cases h4 : xs[7]! = xs[0]!
    · simp [h1, h2, h3, h4]
    by_cases h5 : xs[9]! = xs[0]!
    · simp [h1, h2, h3, h4, h5]
    by_cases h6 : xs[11]! = xs[0]!
    · simp [h1, h2, h3, h4, h5, h6]
    by_cases h7 : xs[13]! = xs[0]!
    · simp [h1, h2, h3, h4, h5, h6, h7]
    by_cases h8 : xs[15]! = xs[0]!
    · simp [h1, h2, h3, h4, h5, h6, h7, h8]
    by_cases h9 : xs[17]! = xs[0]!
    · simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    by_cases h10 : xs[19]! = xs[0]! <;> simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · have hok : (xs.size.toUInt64 == 21) = false := by
      rw [beq_eq_false_iff_ne, ne_eq, ← UInt64.toNat_inj, hn]; exact hs
    simp [hok, hs]

end Examples.Lookup
