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
    match source with
    | .letE name domain value body nondep =>
        if input : PublicArgument.ofType? domain = some (if booleanInput then .boolean else .word) then
          some ⟨name, domain, PublicArgument.ofType_sound input, value, body, nondep,
            booleanLocal_excluded absent⟩
        else none
    | _ => none
  else none

@[simp] theorem booleanScopeBinding_accepts (binding : BooleanScopeBinding booleanInput) :
    booleanScopeBinding? booleanInput binding.expr = some binding := by
  have absent := booleanScopeBinding_not_local binding
  have parsed := PublicArgument.ofType_accepts binding.input
  cases binding
  simp [booleanScopeBinding?, BooleanScopeBinding.expr] at absent ⊢
  simp [absent, parsed]

@[simp] theorem booleanScopeBinding_other (binding : BooleanScopeBinding booleanInput) :
    booleanScopeBinding? (!booleanInput) binding.expr = none := by
  have absent := booleanScopeBinding_not_local binding
  have parsed := PublicArgument.ofType_accepts binding.input
  cases booleanInput <;> simp [booleanScopeBinding?, BooleanScopeBinding.expr] at absent ⊢
  all_goals simp_all

theorem booleanScopeBinding_sound {source : Lean.Expr} {binding : BooleanScopeBinding booleanInput}
    (parsed : booleanScopeBinding? booleanInput source = some binding) : source = binding.expr := by
  cases booleanInput <;> unfold booleanScopeBinding? at parsed
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true] at parsed
  all_goals split at parsed <;> try contradiction
  all_goals split at parsed <;> try contradiction
  all_goals split at parsed <;> try contradiction
  all_goals cases parsed
  all_goals rfl

theorem booleanScopeBinding_sizes {source : Lean.Expr} {binding : BooleanScopeBinding booleanInput}
    (parsed : booleanScopeBinding? booleanInput source = some binding) :
    sizeOf binding.value < sizeOf source ∧ sizeOf binding.body < sizeOf source := by
  rw [booleanScopeBinding_sound parsed]
  exact ⟨binding.value_size, binding.body_size⟩

@[simp] theorem booleanScopeBinding_not_helper (binding : BooleanScopeBinding booleanInput) (other : Bool) :
    booleanHelper? other binding.expr = none := by
  unfold booleanHelper?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  cases booleanInput <;> rcases binding with ⟨name, domain, input, value, body, nondep, extended⟩
  all_goals cases input <;> rfl

@[simp] theorem booleanScopeBinding_not_wrapped (binding : BooleanScopeBinding booleanInput) :
    booleanWrapped? binding.expr = none := by
  unfold booleanWrapped?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rfl

@[simp] theorem booleanScopeBinding_not_negated (binding : BooleanScopeBinding booleanInput) :
    booleanNegated? binding.expr = none := by
  unfold booleanNegated?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rfl

@[simp] theorem booleanScopeBinding_not_joined (binding : BooleanScopeBinding booleanInput) :
    booleanJoined? binding.expr = none := by
  unfold booleanJoined?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rfl

@[simp] theorem booleanScopeBinding_not_related (binding : BooleanScopeBinding booleanInput) :
    booleanRelated? binding.expr = none := by
  unfold booleanRelated?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rfl

@[simp] theorem booleanScopeBinding_not_selected (binding : BooleanScopeBinding booleanInput) :
    booleanSelected? binding.expr = none := by
  unfold booleanSelected?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rfl

@[simp] theorem booleanScopeBinding_not_guarded (binding : BooleanScopeBinding booleanInput) :
    booleanGuardedSelection? binding.expr = none := by
  unfold booleanGuardedSelection?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rfl

@[simp] theorem booleanScopeBinding_not_relation (binding : BooleanScopeBinding booleanInput) :
    booleanRelationSelection? binding.expr = none := by
  unfold booleanRelationSelection?
  rw [dite_eq_left (booleanScopeBinding_not_local binding)]
  rfl

end LeanExe.Extract.Core
