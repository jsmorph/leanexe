import Verified.After

namespace Verified

theorem arguments_moved {S : List Sig} {context params : List Ty} (modes : Nat → Mode)
    (slots : List Slot) (live : Nat → Bool)
    (args : (i : Fin params.length) → Expr S context (params.get i))
    (moves : Fin params.length → Bool)
    (definition : ∀ i, moves i = (modes i == .owned &&
      match (args i).varIndex? with
      | some index => (slots.getD index default).mode == .owned && !live index &&
          !(argsAny fun j => j != i && !(params.get j).scalar && (args j).usesFast index)
      | none => false))
    (variableArgs : ∀ i : Fin params.length, modes i = .owned → ∃ x, args i = .var x) :
    ∀ index, (argsAny fun j => moves j && (args j).uses index) = true →
      ∃ j x, args j = .var x ∧ x.index = index ∧ modes j = .owned ∧
        (slots.getD index default).mode = .owned ∧ live index = false ∧
        ∀ other, other ≠ j → (params.get other).scalar = false →
          (args other).uses index = false := by
  intro index moved
  obtain ⟨j, selected⟩ := argsAny_true.mp moved
  rw [definition j] at selected
  simp only [Bool.and_eq_true, Expr.usesFast_eq, beq_iff_eq] at selected
  obtain ⟨⟨owned, selected⟩, used⟩ := selected
  obtain ⟨x, expression⟩ := variableArgs j owned
  rw [expression] at selected used
  simp only [Expr.varIndex?, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at selected
  simp only [Expr.uses, beq_iff_eq] at used
  subst used
  obtain ⟨⟨variableOwned, dead⟩, others⟩ := selected
  refine ⟨j, x, expression, rfl, owned, variableOwned, dead, fun other different scalar => ?_⟩
  cases uses : (args other).uses x.index with
  | false => rfl
  | true =>
      have selected := le_argsAny (fun k => k != j && !(params.get k).scalar &&
        (args k).uses x.index) other (by rw [scalar, uses]; simp [different])
      rw [others] at selected
      exact nomatch selected

end Verified
