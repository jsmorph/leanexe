import Project.ProofKit.F64OutwardSpec

namespace Project.ProofKit.F64Outward
open CodeLib.IEEE64

theorem accepted_of_behavior (result : Checked) (P : Prop)
    (h : result = rejected ∨ P) (hs : result.status = 0) : P := by
  rcases h with h | h
  · simp [h, rejected] at hs
  · exact h

theorem add_accepted (up : Bool) (a b : UInt64) (hs : (add up a b).status = 0) :
    Finite a ∧ Finite b ∧ Sound up (add up a b) (value a+value b) :=
  accepted_of_behavior _ _ (add_behavior up a b) hs

theorem sub_accepted (up : Bool) (a b : UInt64) (hs : (sub up a b).status = 0) :
    Finite a ∧ Finite b ∧ Sound up (sub up a b) (value a-value b) :=
  accepted_of_behavior _ _ (sub_behavior up a b) hs

theorem mul_accepted (up : Bool) (a b : UInt64) (hs : (mul up a b).status = 0) :
    Finite a ∧ Finite b ∧ Sound up (mul up a b) (value a*value b) :=
  accepted_of_behavior _ _ (mul_behavior up a b) hs

theorem div_accepted (up : Bool) (a b : UInt64) (hs : (div up a b).status = 0) :
    Finite a ∧ Finite b ∧ Wasm.IEEE64.scaledMagnitude b ≠ 0 ∧
      Sound up (div up a b) (value a/value b) :=
  accepted_of_behavior _ _ (div_behavior up a b) hs

theorem sqrt_accepted (up : Bool) (a : UInt64) (hs : (sqrt up a).status = 0) :
    Finite a ∧ 0 ≤ value a ∧ Sound up (sqrt up a) (Real.sqrt (value a)) :=
  accepted_of_behavior _ _ (sqrt_behavior up a) hs

theorem sound_upper {result : Checked} {x : ℝ} (h : Sound true result x) :
    Finite result.value ∧ x ≤ value result.value := ⟨h.2.1, h.2.2⟩

theorem sound_lower {result : Checked} {x : ℝ} (h : Sound false result x) :
    Finite result.value ∧ value result.value ≤ x := ⟨h.2.1, h.2.2⟩

#print axioms accepted_of_behavior
#print axioms div_accepted
end Project.ProofKit.F64Outward
