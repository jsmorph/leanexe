import Verified.FieldsExpr

namespace Verified

theorem argsAny_false (n : Nat) : argsAny (fun _ : Fin n => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [argsAny, ih, Bool.false_or]

def fieldLive {S : List Sig} {Γ ps : List Ty}
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (kept : Nat → Bool)
    (offset k : Nat) : Bool :=
  kept k || argsAny fun i => decide (offset ≤ i.val) && (args i).uses k

theorem fieldLive_zero {S : List Sig} {Γ ps : List Ty}
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (kept : Nat → Bool) (k : Nat) :
    fieldLive args kept 0 k = (kept k || argsAny fun i => (args i).uses k) := by
  simp only [fieldLive, Nat.zero_le, decide_true, Bool.true_and]

theorem fieldLive_end {S : List Sig} {Γ ps : List Ty}
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (kept : Nat → Bool) (k : Nat) :
    fieldLive args kept ps.length k = kept k := by
  have hEmpty : (fun i : Fin ps.length => decide (ps.length ≤ i.val) && (args i).uses k) =
      fun _ => false := by
    funext i
    simp only [Nat.not_le.mpr i.isLt, decide_false, Bool.false_and]
  simp only [fieldLive, hEmpty]
  simp only [argsAny_false, Bool.or_false]

theorem fieldLive_step {S : List Sig} {Γ ps : List Ty}
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (kept : Nat → Bool)
    (i : Fin ps.length) (k : Nat) :
    (fieldLive args kept (i.val + 1) k || (args i).uses k) =
      fieldLive args kept i.val k := by
  rw [Bool.eq_iff_iff]
  simp only [fieldLive, Bool.or_eq_true, argsAny_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((h | ⟨j, hj, hu⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨j, by omega, hu⟩
    · exact Or.inr ⟨i, le_refl _, h⟩
  · rintro (h | ⟨j, hj, hu⟩)
    · exact Or.inl (Or.inl h)
    · by_cases he : j = i
      · subst j
        exact Or.inr hu
      · exact Or.inl (Or.inr ⟨j, by have := Fin.val_ne_of_ne he; omega, hu⟩)

theorem fieldLive_after {S : List Sig} {Γ ps : List Ty}
    (args : (i : Fin ps.length) → Expr S Γ (ps.get i)) (kept : Nat → Bool)
    (i : Fin ps.length) (k : Nat) :
    fieldLive args kept (i.val + 1) k =
      (kept k || argsAny fun j => decide (i.val < j.val) && (args j).uses k) := by
  simp only [fieldLive, Nat.add_one_le_iff]

end Verified
