import LeanExe.Extract.ScalarBooleanRangeSyntax
import LeanExe.Source.ScalarBooleanFunctionChoice

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- A conditional may capture outer values but cannot inspect its local function. -/
def booleanFunctionChoice? : Lean.Expr → Option BooleanFunctionChoice
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type) condition) evidence) yes) no => do
      let output ← booleanType? type
      let condition ← LeanExe.Source.ExprProofBinder.drop? 0 condition
      let evidence ← LeanExe.Source.ExprProofBinder.drop? 0 evidence
      pure ⟨output, condition, evidence, yes, no⟩
  | _ => none

@[simp] theorem booleanFunctionChoice_accepts (choice : BooleanFunctionChoice) :
    booleanFunctionChoice? choice.expr = some choice := by
  cases choice
  simp [BooleanFunctionChoice.expr, booleanFunctionChoice?]

theorem booleanFunctionChoice_sound {source : Lean.Expr} {choice : BooleanFunctionChoice}
    (parsed : booleanFunctionChoice? source = some choice) : source = choice.expr := by
  unfold booleanFunctionChoice? at parsed
  split at parsed
  · rename_i type condition evidence yes no
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨output, ht, test, hc, proof, he, rfl⟩ := parsed
    rw [booleanType_sound ht, LeanExe.Source.ExprProofBinder.drop_sound condition 0 hc,
      LeanExe.Source.ExprProofBinder.drop_sound evidence 0 he]
    rfl
  · contradiction

theorem booleanFunctionChoice_sizes {source : Lean.Expr} {choice : BooleanFunctionChoice}
    (parsed : booleanFunctionChoice? source = some choice) :
    sizeOf choice.yes < sizeOf source ∧ sizeOf choice.no < sizeOf source := by
  rw [booleanFunctionChoice_sound parsed]
  exact choice.arm_sizes

end LeanExe.Extract.Core
