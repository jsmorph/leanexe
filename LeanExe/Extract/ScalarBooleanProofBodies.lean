import LeanExe.Source.ExprProofBinder
import LeanExe.Source.ExprEquality

namespace LeanExe.Extract.Core

/-- Check both proof domains and remove their unused binders before parsing Bool results. -/
def booleanProofBodies? (condition trueDomain yes falseDomain no : Lean.Expr) : Option (Lean.Expr × Lean.Expr) := do
  if LeanExe.Source.ExprEquality.same trueDomain condition &&
      LeanExe.Source.ExprEquality.same falseDomain (.app (.const ``Not []) condition) then
    let t ← LeanExe.Source.ExprProofBinder.drop? 0 yes
    let e ← LeanExe.Source.ExprProofBinder.drop? 0 no
    pure (t, e)
  else none

@[simp] theorem booleanProofBodies_accepts (condition yes no : Lean.Expr) :
    booleanProofBodies? condition condition (LeanExe.Source.ExprProofBinder.lift 0 yes)
      (.app (.const ``Not []) condition) (LeanExe.Source.ExprProofBinder.lift 0 no) = some (yes, no) := by
  simp [booleanProofBodies?]

theorem booleanProofBodies_sound {condition trueDomain yes falseDomain no t e : Lean.Expr}
    (parsed : booleanProofBodies? condition trueDomain yes falseDomain no = some (t, e)) :
    trueDomain = condition ∧ falseDomain = .app (.const ``Not []) condition ∧
      yes = LeanExe.Source.ExprProofBinder.lift 0 t ∧ no = LeanExe.Source.ExprProofBinder.lift 0 e := by
  unfold booleanProofBodies? at parsed
  split at parsed
  · rename_i domains
    simp only [Bool.and_eq_true, LeanExe.Source.ExprEquality.same_eq_true] at domains
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨t', ht, e', he, rfl, rfl⟩ := parsed
    exact ⟨domains.1, domains.2, LeanExe.Source.ExprProofBinder.drop_sound yes 0 ht,
      LeanExe.Source.ExprProofBinder.drop_sound no 0 he⟩
  · contradiction

theorem booleanProofBodies_sizes {condition trueDomain yes falseDomain no t e : Lean.Expr}
    (parsed : booleanProofBodies? condition trueDomain yes falseDomain no = some (t, e)) :
    sizeOf t ≤ sizeOf yes ∧ sizeOf e ≤ sizeOf no := by
  obtain ⟨_, _, yesShape, noShape⟩ := booleanProofBodies_sound parsed
  rw [yesShape, noShape]
  exact ⟨LeanExe.Source.ExprProofBinder.lift_size t 0, LeanExe.Source.ExprProofBinder.lift_size e 0⟩

end LeanExe.Extract.Core
