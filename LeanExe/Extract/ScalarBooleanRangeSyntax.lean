import LeanExe.Extract.ScalarBooleanType
import LeanExe.Extract.ScalarDo
import LeanExe.Source.ScalarBooleanWrapper

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- A standard word-to-Boolean bind preserves its exact continuation domain. -/
def booleanRangeBindTypes? (input domain output : Lean.Expr) : Option (ResultType × BooleanType) := do
  let first ← scalarResultType? input
  let last ← booleanType? output
  if input = domain then some (first, last) else none

@[simp] theorem booleanRangeBindTypes_accepts (input : ResultType) (output : BooleanType) :
    booleanRangeBindTypes? input.expr input.expr output.expr = some (input, output) := by
  simp [booleanRangeBindTypes?]

theorem booleanRangeBindTypes_sound {input domain output : Lean.Expr}
    {first : ResultType} {last : BooleanType}
    (parsed : booleanRangeBindTypes? input domain output = some (first, last)) :
    input = first.expr ∧ domain = first.expr ∧ output = last.expr := by
  simp only [booleanRangeBindTypes?, bind, Option.bind_eq_some_iff] at parsed
  obtain ⟨a, ha, b, hb, accepted⟩ := parsed
  split at accepted
  · rename_i same
    cases accepted
    exact ⟨scalarResultType_sound ha, same ▸ scalarResultType_sound ha, booleanType_sound hb⟩
  · contradiction

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
