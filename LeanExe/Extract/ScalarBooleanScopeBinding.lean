import LeanExe.Source.ScalarBooleanScopeBinding
import LeanExe.Extract.ScalarBooleanRelationSelection

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

@[simp] theorem booleanScopeBinding_not_local (binding : BooleanScopeBinding booleanInput) :
    booleanLocalOperands? binding.expr = none := by
  cases found : booleanLocalOperands? binding.expr with
  | none => rfl
  | some expression => exact False.elim (binding.extended expression (booleanLocalOperands_sound found))

def booleanScopeBinding? (booleanInput : Bool) (source : Lean.Expr) : Option (BooleanScopeBinding booleanInput) :=
  if absent : booleanLocalOperands? source = none then
    match same : source with
    | .letE name domain value body nondep =>
        if input : PublicArgument.ofType? domain = some (if booleanInput then .boolean else .word) then
          some ⟨name, domain, PublicArgument.ofType_sound input, value, body, .letE nondep,
            booleanLocal_excluded absent⟩
        else none
    | .app (.lam name domain body binder) value =>
        if input : PublicArgument.ofType? domain = some (if booleanInput then .boolean else .word) then
          some ⟨name, domain, PublicArgument.ofType_sound input, value, body, .application binder,
            booleanLocal_excluded absent⟩
        else none
    | .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero]))) inputType) output) value)
        (.lam name domain body binder) =>
        if domains : inputType = domain then
          match resultFound : booleanType? output with
          | some result =>
              if input : PublicArgument.ofType? inputType = some (if booleanInput then .boolean else .word) then
                let form := BooleanScopeBindingForm.monadic binder result
                have exactSource : source = form.expr name inputType value body := by
                  rw [same, ← domains, booleanType_sound resultFound]
                  rfl
                some ⟨name, inputType, PublicArgument.ofType_sound input, value, body, form,
                  fun expression equal => booleanLocal_excluded absent expression
                    (same.symm.trans (exactSource.trans equal))⟩
              else none
          | none => none
        else none
    | _ => none
  else none

@[simp] theorem booleanScopeBinding_accepts (binding : BooleanScopeBinding booleanInput) :
    booleanScopeBinding? booleanInput binding.expr = some binding := by
  have absent := booleanScopeBinding_not_local binding
  have parsed := PublicArgument.ofType_accepts binding.input
  rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  cases form with
  | letE nondep =>
    simp [booleanScopeBinding?, BooleanScopeBinding.expr, BooleanScopeBindingForm.expr,
      BooleanScopeBindingForm.base, BooleanBindingForm.expr] at absent ⊢
    simp [absent, parsed]
  | application binder =>
    simp [booleanScopeBinding?, BooleanScopeBinding.expr, BooleanScopeBindingForm.expr,
      BooleanScopeBindingForm.base, BooleanBindingForm.expr] at absent ⊢
    simp [absent, parsed]
  | monadic binder result =>
    simp [booleanScopeBinding?, BooleanScopeBinding.expr, BooleanScopeBindingForm.expr,
      BooleanScopeBindingForm.base, BooleanBindingForm.expr] at absent ⊢
    simp [absent, parsed]
    split <;> simp_all
    simp_all only [booleanType_accepts, Option.some.injEq]

@[simp] theorem booleanScopeBinding_other (binding : BooleanScopeBinding booleanInput) :
    booleanScopeBinding? (!booleanInput) binding.expr = none := by
  have absent := booleanScopeBinding_not_local binding
  have parsed := PublicArgument.ofType_accepts binding.input
  cases booleanInput <;> rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  all_goals cases form <;> simp [booleanScopeBinding?, BooleanScopeBinding.expr,
    BooleanScopeBindingForm.expr, BooleanScopeBindingForm.base, BooleanBindingForm.expr] at absent ⊢
  all_goals simp_all
  all_goals split <;> rfl

theorem booleanScopeBinding_sound {source : Lean.Expr} {binding : BooleanScopeBinding booleanInput}
    (parsed : booleanScopeBinding? booleanInput source = some binding) : source = binding.expr := by
  cases booleanInput
  all_goals
    unfold booleanScopeBinding? at parsed
    simp only [Bool.false_eq_true, ite_false, ite_true] at parsed
    split at parsed <;> try contradiction
    split at parsed
    · split at parsed <;> try contradiction
      cases parsed
      rfl
    · split at parsed <;> try contradiction
      cases parsed
      rfl
    · rename_i inputType output value name domain body binder same
      split at parsed
      · rename_i domains
        split at parsed
        · rename_i result resultFound
          split at parsed <;> try contradiction
          cases parsed
          simp only [BooleanScopeBinding.expr, BooleanScopeBindingForm.expr,
            BooleanScopeBindingForm.base, BooleanBindingForm.expr]
          rw [← domains, booleanType_sound resultFound]
        · contradiction
      · contradiction
    · contradiction

theorem booleanScopeBinding_sizes {source : Lean.Expr} {binding : BooleanScopeBinding booleanInput}
    (parsed : booleanScopeBinding? booleanInput source = some binding) :
    sizeOf binding.value < sizeOf source ∧ sizeOf binding.body < sizeOf source := by
  rw [booleanScopeBinding_sound parsed]
  exact ⟨binding.value_size, binding.body_size⟩

@[simp] theorem booleanScopeBinding_not_helper (binding : BooleanScopeBinding booleanInput) (other : Bool) :
    booleanHelper? other binding.expr = none := by
  unfold booleanHelper?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  cases booleanInput <;> rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  all_goals cases form
  all_goals first | rfl | (cases input <;> rfl)

@[simp] theorem booleanScopeBinding_not_wrapped (binding : BooleanScopeBinding booleanInput) :
    booleanWrapped? binding.expr = none := by
  unfold booleanWrapped?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  cases form <;> rfl

@[simp] theorem booleanScopeBinding_not_negated (binding : BooleanScopeBinding booleanInput) :
    booleanNegated? binding.expr = none := by
  unfold booleanNegated?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  cases form <;> rfl

@[simp] theorem booleanScopeBinding_not_joined (binding : BooleanScopeBinding booleanInput) :
    booleanJoined? binding.expr = none := by
  unfold booleanJoined?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  cases form <;> rfl

@[simp] theorem booleanScopeBinding_not_related (binding : BooleanScopeBinding booleanInput) :
    booleanRelated? binding.expr = none := by
  unfold booleanRelated?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  cases form <;> rfl

@[simp] theorem booleanScopeBinding_not_selected (binding : BooleanScopeBinding booleanInput) :
    booleanSelected? binding.expr = none := by
  unfold booleanSelected?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  cases form <;> rfl

@[simp] theorem booleanScopeBinding_not_guarded (binding : BooleanScopeBinding booleanInput) :
    booleanGuardedSelection? binding.expr = none := by
  unfold booleanGuardedSelection?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  cases form <;> rfl

@[simp] theorem booleanScopeBinding_not_relation (binding : BooleanScopeBinding booleanInput) :
    booleanRelationSelection? binding.expr = none := by
  unfold booleanRelationSelection?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rcases binding with ⟨name, domain, input, value, body, form, extended⟩
  cases form <;> rfl

end LeanExe.Extract.Core
