import LeanExe.Source.ScalarBooleanWrapped
import LeanExe.Extract.ScalarBooleanHelper

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Preserve the exact standard wrapper and its unparsed Boolean body. -/
def booleanWrapperParts? : Lean.Expr → Option (BooleanWrapper × Lean.Expr)
  | .app (.app (.const ``Id.run [.zero]) type) body => do
      let annotation ← booleanType? type
      pure (.run annotation, body)
  | .app (.app (.app (.app (.const ``Pure.pure [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero])))) type) body => do
      let annotation ← booleanType? type
      pure (.pure annotation, body)
  | .mdata data body => some (.metadata data, body)
  | _ => none

@[simp] theorem booleanWrapperParts_accepts (wrapper : BooleanWrapper) (body : Lean.Expr) :
    booleanWrapperParts? (wrapper.expr body) = some (wrapper, body) := by
  cases wrapper <;> simp [booleanWrapperParts?, BooleanWrapper.expr, BooleanIdentity.run, BooleanIdentity.pure]

theorem booleanWrapperParts_sound {source : Lean.Expr} {wrapper : BooleanWrapper} {body : Lean.Expr}
    (parsed : booleanWrapperParts? source = some (wrapper, body)) : source = wrapper.expr body := by
  unfold booleanWrapperParts? at parsed
  split at parsed
  · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨type, found, rfl, rfl⟩ := parsed
    rw [booleanType_sound found]
    rfl
  · simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
    obtain ⟨type, found, rfl, rfl⟩ := parsed
    rw [booleanType_sound found]
    rfl
  · cases parsed
    rfl
  · contradiction

@[simp] theorem booleanWrapped_not_local (value : BooleanWrapped) :
    booleanLocalOperands? value.expr = none := by
  cases found : booleanLocalOperands? value.expr with
  | none => rfl
  | some expression => exact False.elim (value.extended expression (booleanLocalOperands_sound found))

def booleanWrapped? (source : Lean.Expr) : Option BooleanWrapped :=
  if absent : booleanLocalOperands? source = none then
    match parsed : booleanWrapperParts? source with
    | some (wrapper, body) => some ⟨wrapper, body,
        fun expression same => booleanLocal_excluded absent expression ((booleanWrapperParts_sound parsed).trans same)⟩
    | none => none
  else none

@[simp] theorem booleanWrapped_accepts (value : BooleanWrapped) :
    booleanWrapped? value.expr = some value := by
  have absent := booleanWrapped_not_local value
  rcases value with ⟨wrapper, body, extended⟩
  simp only [BooleanWrapped.expr] at absent ⊢
  simp only [booleanWrapped?, dite_eq_left absent]
  split
  · rename_i actualWrapper actualBody found
    have same := Option.some.inj ((booleanWrapperParts_accepts wrapper body).symm.trans found)
    cases same
    rfl
  · rename_i found
    rw [booleanWrapperParts_accepts] at found
    contradiction

theorem booleanWrapped_sound {source : Lean.Expr} {value : BooleanWrapped}
    (parsed : booleanWrapped? source = some value) : source = value.expr := by
  unfold booleanWrapped? at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  rename_i wrapper body found
  cases parsed
  exact booleanWrapperParts_sound found

@[simp] theorem booleanWrapped_not_helper (value : BooleanWrapped) (booleanInput : Bool) :
    booleanHelper? booleanInput value.expr = none := by
  unfold booleanHelper?
  rw [dite_eq_left (booleanWrapped_not_local value)]
  rcases value with ⟨wrapper, body, extended⟩
  cases wrapper <;> rfl

theorem booleanWrapped_size {source : Lean.Expr} {value : BooleanWrapped}
    (parsed : booleanWrapped? source = some value) : sizeOf value.body < sizeOf source := by
  rw [booleanWrapped_sound parsed]
  exact value.body_size

end LeanExe.Extract.Core
