import Project.ProofKit.F32SumRangeCheck
import Project.ProofKit.F32SumError

namespace Project.ProofKit.F32SumRangeCertificate

theorem prefix_value (input : Nat → UInt32) (bound count : Nat) :
    (checkedPrefix input bound count).1 = F32SumError.sumPrefix input count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [checkedPrefix, F32SumError.sumPrefix_succ, ih, F32Add.add_eq]

theorem prefix_checks (input : Nat → UInt32) (bound count : Nat)
    (h : (checkedPrefix input bound count).2 = true) :
    ∀ i < count, F32RangeCertificate.addition (F32SumError.sumPrefix input i) (input i) bound = true := by
  induction count with
  | zero => intro i hi; omega
  | succ count ih =>
    change ((checkedPrefix input bound count).2 && F32RangeCertificate.addition (checkedPrefix input bound count).1 (input count) bound) = true at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hp, ha⟩ := h
    rw [prefix_value] at ha
    intro i hi
    by_cases he : i = count
    · simpa only [he] using ha
    · exact ih hp i (by omega)

theorem ranges (input : Nat → UInt32) (bound count : Nat)
    (h : (checkedPrefix input bound count).2 = true) :
    ∀ i < count, (Wasm.IEEE32.scaledValue (F32SumError.sumPrefix input i) +
      Wasm.IEEE32.scaledValue (input i)).natAbs < 2 ^ bound := by
  intro i hi
  have hc := prefix_checks input bound count h i hi
  simp only [F32RangeCertificate.addition, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.2

#print axioms prefix_checks
#print axioms ranges
end Project.ProofKit.F32SumRangeCertificate
