import Project.ProofKit.F32HornerRangeCheck
import Project.ProofKit.F32HornerError

namespace Project.ProofKit.F32HornerRangeCertificate

theorem prefix_value (input initial : UInt32) (coefficient : Nat → UInt32)
    (mulBound addBound count : Nat) :
    (checkedPrefix input initial coefficient mulBound addBound count).1 =
      F32HornerError.compute input initial coefficient count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [checkedPrefix, F32HornerError.compute_succ, ih]

theorem checks (input initial : UInt32) (coefficient : Nat → UInt32)
    (mulBound addBound count : Nat)
    (h : (checkedPrefix input initial coefficient mulBound addBound count).2 = true) :
    ∀ i < count,
      F32RangeCertificate.multiplication (F32HornerError.compute input initial coefficient i) input mulBound = true ∧
      F32RangeCertificate.addition (LeanExe.Float32.mulBits
        (F32HornerError.compute input initial coefficient i) input) (coefficient i) addBound = true := by
  induction count with
  | zero => intro i hi; omega
  | succ count ih =>
    simp only [checkedPrefix, Bool.and_eq_true] at h
    obtain ⟨⟨hp, hm⟩, ha⟩ := h
    rw [prefix_value] at hm ha
    intro i hi
    by_cases he : i = count
    · simpa only [he] using And.intro hm ha
    · exact ih hp i (by omega)

#print axioms checks
end Project.ProofKit.F32HornerRangeCertificate
