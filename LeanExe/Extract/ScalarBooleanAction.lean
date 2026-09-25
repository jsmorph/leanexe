import LeanExe.Source.ScalarBooleanAction
import LeanExe.Extract.ScalarBooleanLocalSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

@[simp] theorem booleanLocalOperands_booleanPure (body : Lean.Expr) :
    booleanLocalOperands? (BooleanIdentity.pure body) = none := rfl
@[simp] theorem booleanLocalOperands_booleanRun (body : Lean.Expr) :
    booleanLocalOperands? (BooleanIdentity.run body) = none := rfl
@[simp] theorem booleanLocalOperands_metadata (data : Lean.MData) (body : Lean.Expr) :
    booleanLocalOperands? (.mdata data body) = none := rfl

/-- Direct Boolean values or exact standard pure Id wrappers. -/
def booleanAction? (source : Lean.Expr) : Option BooleanAction :=
  match booleanLocalOperands? source with
  | some value => some (.value value)
  | none =>
      match source with
      | .app (.app (.const ``Id.run [.zero]) (.const ``Bool [])) body =>
          (booleanAction? body).map BooleanAction.run
      | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
          (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
            (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
              (.const ``Id.instMonad [.zero])))) (.const ``Bool [])) body =>
          (booleanAction? body).map BooleanAction.pure
      | .mdata data body => (booleanAction? body).map (BooleanAction.metadata data)
      | _ => none
termination_by sizeOf source

theorem booleanAction_accepts (action : BooleanAction) : booleanAction? action.expr = some action := by
  induction action with
  | value expression => rw [BooleanAction.expr, booleanAction?.eq_def, booleanLocalOperands_expr]
  | run body ih =>
    rw [BooleanAction.expr, booleanAction?.eq_def, booleanLocalOperands_booleanRun]
    simpa only [BooleanIdentity.run, Option.map_some] using congrArg (Option.map BooleanAction.run) ih
  | pure body ih =>
    rw [BooleanAction.expr, booleanAction?.eq_def, booleanLocalOperands_booleanPure]
    simpa only [BooleanIdentity.pure, Option.map_some] using congrArg (Option.map BooleanAction.pure) ih
  | metadata data body ih =>
    rw [BooleanAction.expr, booleanAction?.eq_def, booleanLocalOperands_metadata]
    simpa only [Option.map_some] using congrArg (Option.map (BooleanAction.metadata data)) ih

theorem booleanAction_sound {source : Lean.Expr} {action : BooleanAction}
    (parsed : booleanAction? source = some action) : source = action.expr := by
  rw [booleanAction?.eq_def] at parsed
  split at parsed
  · rename_i expression found
    cases parsed
    exact booleanLocalOperands_sound found
  · split at parsed
    · obtain ⟨body, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      simp only [BooleanAction.expr, BooleanIdentity.run, booleanAction_sound found]
    · obtain ⟨body, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      simp only [BooleanAction.expr, BooleanIdentity.pure, booleanAction_sound found]
    · obtain ⟨body, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      simp only [BooleanAction.expr, booleanAction_sound found]
    · contradiction
termination_by sizeOf source

theorem booleanAction_size {source : Lean.Expr} {action : BooleanAction}
    (parsed : booleanAction? source = some action) {operand : Lean.Expr}
    (member : operand ∈ action.leaf.operands) : sizeOf operand < sizeOf source := by
  rw [booleanAction_sound parsed]
  exact action.operands_size member

end LeanExe.Extract.Core
