import Project.ProofKit.F32DotRangeCheck
import Project.ProofKit.F32DotRanges

namespace Project.ProofKit.F32DotRangeCertificate

theorem prefix_value (x w : Nat → UInt32) (mulBound addBound count : Nat) :
    (checkedPrefix x w mulBound addBound count).1 = F32DotError.compute x w count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [checkedPrefix, F32DotError.compute, F32SumError.sumPrefix_succ] at *; rw [ih]

theorem checks (x w : Nat → UInt32) (mulBound addBound count : Nat)
    (h : (checkedPrefix x w mulBound addBound count).2 = true) :
    ∀ i < count,
      F32RangeCertificate.multiplication (x i) (w i) mulBound = true ∧
      F32RangeCertificate.addition (F32DotError.compute x w i)
        (LeanExe.Float32.mulBits (x i) (w i)) addBound = true := by
  induction count with
  | zero => intro i hi; omega
  | succ count ih =>
    simp only [checkedPrefix, Bool.and_eq_true] at h
    obtain ⟨⟨hp, hm⟩, ha⟩ := h
    rw [prefix_value] at ha
    intro i hi
    by_cases he : i = count
    · simpa only [he] using And.intro hm ha
    · exact ih hp i (by omega)

theorem ranges (x w : Nat → UInt32) (mulBound addBound count : Nat)
    (h : (checkedPrefix x w mulBound addBound count).2 = true) :
    F32DotError.Ranges x w count ⟨fun _ => mulBound, fun _ => addBound⟩ := by
  have hc := checks x w mulBound addBound count h
  have hm (i : Nat) (hi : i < count) := (hc i hi).1
  have ha (i : Nat) (hi : i < count) := (hc i hi).2
  simp only [F32RangeCertificate.multiplication, F32RangeCertificate.addition,
    Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hm ha
  exact ⟨fun i hi => (hm i hi).1, fun i hi => (hm i hi).2.1,
    fun i hi => (hm i hi).2.2.1, fun i hi => (hm i hi).2.2.2.1,
    fun i hi => (hm i hi).2.2.2.2, fun i hi => (ha i hi).2.2.1,
    fun i hi => (ha i hi).2.2.2⟩

#print axioms ranges
end Project.ProofKit.F32DotRangeCertificate
