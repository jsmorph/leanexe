import LeanExe.Extract.ScalarBooleanRangeSyntax
import LeanExe.Source.ScalarBooleanFunctionChoice

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- A conditional may capture outer values but cannot inspect its local function. -/
def booleanFunctionChoice? (source : Lean.Expr) : Option BooleanFunctionChoice :=
  match source with
  | .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type) condition) evidence) yes) no => do
      let output ← booleanType? type
      let condition ← LeanExe.Source.ExprProofBinder.drop? 0 condition
      let evidence ← LeanExe.Source.ExprProofBinder.drop? 0 evidence
      pure (.mk output condition evidence yes no)
  | .letE name type value (.bvar 0) nondep => do
      let type ← booleanType? type
      let inner ← booleanFunctionChoice? value
      pure (.savedResult name type nondep inner)
  | source =>
      match _parsed : booleanRangeWrapper? source with
      | none => none
      | some (wrapper, body) => do
          let inner ← booleanFunctionChoice? body
          pure (.wrapped wrapper inner)
termination_by sizeOf source
decreasing_by
  all_goals first | (simp_wf; omega) | exact booleanRangeWrapper_size _parsed

theorem booleanFunctionChoice_wrapped (wrapper : BooleanWrapper) (body : Lean.Expr) :
    booleanFunctionChoice? (wrapper.expr body) = (do
      let inner ← booleanFunctionChoice? body
      pure (.wrapped wrapper inner)) := by
  have parsed := booleanRangeWrapper_accepts wrapper body
  cases wrapper <;> simp only [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure] at parsed ⊢
  all_goals rw [booleanFunctionChoice?.eq_def]
  all_goals split <;> simp_all
  all_goals split <;> simp_all

@[simp] theorem booleanFunctionChoice_accepts (choice : BooleanFunctionChoice) :
    booleanFunctionChoice? choice.expr = some choice := by
  induction choice with
  | mk output condition evidence yes no =>
    simp [BooleanFunctionChoice.expr, booleanFunctionChoice?]
  | wrapped wrapper inner ih =>
    rw [BooleanFunctionChoice.expr, booleanFunctionChoice_wrapped]
    simp [ih]
  | savedResult name type nondep inner ih =>
    simp [BooleanFunctionChoice.expr, booleanFunctionChoice?, ih]

theorem booleanFunctionChoice_sound {source : Lean.Expr} {choice : BooleanFunctionChoice}
    (parsed : booleanFunctionChoice? source = some choice) : source = choice.expr := by
  induction source using (measure (fun e : Lean.Expr => sizeOf e)).wf.induction generalizing choice with
  | h source ih =>
    rw [booleanFunctionChoice?.eq_def] at parsed
    split at parsed
    · rename_i type condition evidence yes no
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨output, ht, test, hc, proof, he, rfl⟩ := parsed
      rw [booleanType_sound ht, LeanExe.Source.ExprProofBinder.drop_sound condition 0 hc,
        LeanExe.Source.ExprProofBinder.drop_sound evidence 0 he]
      rfl
    · rename_i name type value nondep
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨output, typed, inner, found, rfl⟩ := parsed
      have smaller : sizeOf value < sizeOf (Lean.Expr.letE name type value (.bvar 0) nondep) := by simp; omega
      rw [booleanType_sound typed, ih value smaller found]
      rfl
    · split at parsed
      · contradiction
      · rename_i wrapper body matched
        simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
        obtain ⟨inner, found, rfl⟩ := parsed
        rw [booleanRangeWrapper_sound matched, ih body (booleanRangeWrapper_size matched) found]
        rfl

theorem booleanFunctionChoice_sizes {source : Lean.Expr} {choice : BooleanFunctionChoice}
    (parsed : booleanFunctionChoice? source = some choice) :
    sizeOf choice.yes < sizeOf source ∧ sizeOf choice.no < sizeOf source := by
  rw [booleanFunctionChoice_sound parsed]
  exact choice.arm_sizes

end LeanExe.Extract.Core
