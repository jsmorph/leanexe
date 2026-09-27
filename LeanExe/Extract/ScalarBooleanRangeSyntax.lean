import LeanExe.Extract.ScalarBooleanType
import LeanExe.Source.ScalarBooleanWrapper

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Exact Boolean Id wrappers and metadata; arbitrary wrapper heads are rejected. -/
def booleanRangeWrapper? : Lean.Expr → Option (BooleanWrapper × Lean.Expr)
  | .app (.app (.const ``Id.run [.zero]) type) body => do
      let type ← booleanType? type
      pure (.run type, body)
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero])))) type) body => do
      let type ← booleanType? type
      pure (.pure type, body)
  | .mdata data body => some (.metadata data, body)
  | _ => none

@[simp] theorem booleanRangeWrapper_accepts (wrapper : BooleanWrapper) (body : Lean.Expr) :
    booleanRangeWrapper? (wrapper.expr body) = some (wrapper, body) := by
  cases wrapper <;> simp [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure, booleanRangeWrapper?]

theorem booleanRangeWrapper_sound {source : Lean.Expr} {wrapper : BooleanWrapper} {body : Lean.Expr}
    (parsed : booleanRangeWrapper? source = some (wrapper, body)) : source = wrapper.expr body := by
  unfold booleanRangeWrapper? at parsed
  split at parsed
  · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨type, valid, same⟩ := parsed
    cases same
    rw [booleanType_sound valid]
    rfl
  · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨type, valid, same⟩ := parsed
    cases same
    rw [booleanType_sound valid]
    rfl
  · cases Option.some.inj parsed
    rfl
  · contradiction

theorem booleanRangeWrapper_size {source : Lean.Expr} {wrapper : BooleanWrapper} {body : Lean.Expr}
    (parsed : booleanRangeWrapper? source = some (wrapper, body)) : sizeOf body < sizeOf source := by
  rw [booleanRangeWrapper_sound parsed]
  exact wrapper.body_size body

theorem booleanRangeWrapper_not_let (wrapper : BooleanWrapper) (body : Lean.Expr)
    (name : Lean.Name) (type value tail : Lean.Expr) (nondep : Bool) :
    wrapper.expr body ≠ .letE name type value tail nondep := by
  cases wrapper <;> simp [BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure]

end LeanExe.Extract.Core
