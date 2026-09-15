import Project.ProofKit.F64OutwardAccepted

namespace Project.ProofKit.F64Outward
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64Adjacent

noncomputable def enclosureWidth (rounded : UInt64) : ℝ :=
  value (nextUp rounded) - value (nextDown rounded)

theorem endpoint_error (up : Bool) (rounded : UInt64) (x : ℝ)
    (hs : (endpoint up rounded).status = 0)
    (he : Finite rounded → value (nextDown rounded) ≤ x ∧ x ≤ value (nextUp rounded)) :
    |value (endpoint up rounded).value - x| ≤ enclosureWidth rounded := by
  unfold endpoint at hs ⊢
  dsimp only at hs ⊢
  split_ifs at hs ⊢ with hf hn
  · have he := he ((finiteBits_iff _).mp hf)
    cases up <;> simp only [neighbor, Bool.false_eq_true, ↓reduceIte, enclosureWidth]
    · rw [abs_of_nonpos (by linarith only [he.1])]
      linarith only [he.2]
    · rw [abs_of_nonneg (by linarith only [he.2])]
      linarith only [he.1]
  all_goals exact False.elim ((by decide : (1 : UInt64) ≠ 0) hs)

theorem div_error (up : Bool) (a b : UInt64) (hs : (div up a b).status = 0) :
    |value (div up a b).value - value a / value b| ≤ enclosureWidth (Wasm.IEEE64.div a b) := by
  have hp := div_accepted up a b hs
  unfold div at hs ⊢
  split_ifs at hs ⊢ with hg
  · exact endpoint_error up _ _ hs (div_enclosure a b hp.1 hp.2.1 hp.2.2.1)
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) hs)

#print axioms endpoint_error
#print axioms div_error
end Project.ProofKit.F64Outward
